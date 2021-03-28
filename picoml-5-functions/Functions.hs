module Functions where

import Control.Applicative (liftA2)
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer

import Data.Functor (($>))
import Data.List (intercalate)
import qualified Data.Set as S

import Text.Parsec hiding (State, parse)
import qualified Text.Parsec as Parsec (parse)
import Text.Parsec.Language
import Text.Parsec.Expr
import qualified Text.Parsec.Token as T
import Text.Parsec.String

--------------------------------------------------------------------------------------
--
-- Language Data Types
--
--------------------------------------------------------------------------------------

data Statement
  = AnonStmt Exp        -- e;;
  | LetStmt  String Exp -- let x = e;;
  | LetRecStmt String String Exp -- let rec f x = e;;
  deriving (Eq, Show)

data Exp
  = ConstExp Const
  | VarExp   String
  | IfExp    Exp Exp Exp
  | ListExp  [Exp]
  | MonopExp Monop Exp
  | BinopExp Exp Binop Exp
  | FunExp   String Exp
  | AppExp   Exp Exp
  | LetInExp String Exp Exp
  | LetRecInExp String String Exp Exp
  deriving (Eq, Ord, Show)

data Const
  = IntConst    Integer
  | FloatConst  Double
  | BoolConst   Bool
  | StringConst String
  | UnitConst
  | NilConst
  deriving (Eq, Ord, Show)

data Monop
  = IntNegOp | NotOp
  deriving (Eq, Ord, Show)

data Binop
  = IntPlusOp | IntSubOp | IntTimesOp | IntDivOp
  | FloatPlusOp | FloatSubOp | FloatTimesOp | FloatDivOp
  | EqOp | LtOp | LeqOp | GtOp | GeqOp
  | AndOp | OrOp
  | ConsOp
  | StrCatOp
  deriving (Eq, Ord, Show)

data Monotype
  = TyCon String [Monotype]
  | TyVar TyVar
  deriving (Eq, Show)

type TyVar = Int

data Polytype = Forall [TyVar] Monotype
  deriving (Eq, Show)

data Val
  = IntVal    Integer
  | FloatVal  Double
  | BoolVal   Bool
  | StringVal String
  | UnitVal
  | ListVal [Val] -- we could also write NilVal | ConsVal Val Val,
                  -- but this is easier to work with for our purposes.
  | CloVal String Exp Sigma
  deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------------
--
-- Utilities
--
--------------------------------------------------------------------------------------

type Env a = [(String, a)]
type Gamma = Env Polytype
type Sigma = Env Val

lookupEnv :: Env a -> String -> Maybe a
lookupEnv = flip lookup -- talk about combinators again

insertEnv :: String -> a -> Env a -> Env a
insertEnv s a env = (s,a):env

unionEnv :: Env a -> Env a -> Env a
unionEnv = (++)

--------------------------------------------------------------------------------------
--
-- Parsing
--
--------------------------------------------------------------------------------------

picomlDef :: LanguageDef st
picomlDef = emptyDef
  { T.reservedOpNames =
    [ "=", "->", ";;"
    , "+", "-", "*", "/"
    , "+.", "-.", "*.", "/."
    , "<", ">", "<=", ">="
    , "::"
    , "&&", "||"
    , "^"
    ]
  , T.reservedNames =
    [ "true", "false"
    , "let", "rec", "in"
    , "if", "then", "else"
    ]
  }

picoml :: T.TokenParser st
picoml = T.makeTokenParser picomlDef

lexeme, parens, brackets :: Parser a -> Parser a
lexeme = T.lexeme picoml
parens = T.parens picoml
brackets = T.brackets picoml

identifier, stringLiteral :: Parser String
identifier    = T.identifier picoml
stringLiteral = T.stringLiteral picoml

reserved, reservedOp :: String -> Parser ()
reserved   = T.reserved picoml
reservedOp = T.reservedOp picoml

whitespace :: Parser ()
whitespace = T.whiteSpace picoml

-- this will evolve as we add to the interpreter
parse :: String -> Either ParseError Statement
parse = Parsec.parse (whitespace *> parseStmt <* eof) "<interactive>"

parseStmt :: Parser Statement
parseStmt = do
  stmt <- parseLetStmt <|> parseAnonStmt
  _    <- reservedOp ";;"
  return stmt

parseLetStmt :: Parser Statement
parseLetStmt = do
  _    <- reserved "let"
  mrec <- optionMaybe $ reserved "rec" >> identifier
  name <- identifier
  _    <- reservedOp "="
  body <- parseExp
  manon <- optionMaybe $ reserved "in" >> parseExp
  return $ case manon of
    Nothing -> case mrec of
      Nothing -> LetStmt name body
      Just f  -> LetRecStmt f name body
    Just e -> case mrec of
      Nothing -> AnonStmt $ LetInExp name body e
      Just f  -> AnonStmt $ LetRecInExp f name body e

parseAnonStmt :: Parser Statement
parseAnonStmt = AnonStmt <$> parseExp

parseExp :: Parser Exp
parseExp = parseIf
           <|> parseFun
           <|> parseLet
           <|> parseOpExp
           <?> "expression"

parseOpExp :: Parser Exp
parseOpExp = buildExpressionParser table parseAExp <?> "operator expression"
  where
    table = [ [prefix "~" IntNegOp]
            , [ binary "*" IntTimesOp AssocLeft, binary "/" IntDivOp AssocLeft
              , binary "*." FloatTimesOp AssocLeft, binary "/." FloatDivOp AssocLeft
              ]
            , [ binary "+" IntPlusOp AssocLeft, binary "-" IntSubOp AssocLeft
              , binary "+." FloatPlusOp AssocLeft, binary "-." FloatSubOp AssocLeft
              ]
            , [ binary "::" ConsOp AssocRight ]
            , [ binary "^" StrCatOp AssocRight ]
            , [ binary "=" EqOp AssocLeft, binary "<" LtOp AssocLeft
              , binary ">" GtOp AssocLeft, binary "<=" LeqOp AssocLeft
              , binary ">=" GeqOp AssocLeft
              ]
            , [ binary "&&" AndOp AssocRight, binary "||" OrOp AssocRight ]
            ]

binary name op = Infix go
  where go = do
          _ <- reservedOp name
          return $ \v1 v2 -> BinopExp v1 op v2

prefix name op = Prefix $ reservedOp name $> MonopExp op

parseAExp :: Parser Exp
parseAExp = chainl1 parseAtomicExp (pure AppExp)
            <?> "application expression"

parseAtomicExp :: Parser Exp
parseAtomicExp = ConstExp <$> parseConst
                 <|> parseVar
                 <|> parens parseExp
                 <|> parseList
                 <?> "value expression"

parseConst :: Parser Const
parseConst = (reserved "true" $> BoolConst True)
             <|> (reserved "false" $> BoolConst False)
             <|> try (parens (pure ()) $> UnitConst)
             <|> parseNumber
             <|> parseString
             <?> "literal"

parseVar :: Parser Exp
parseVar = VarExp <$> identifier <?> "name"

parseIf :: Parser Exp
parseIf = do
  _  <- reserved "if"
  e1 <- parseExp
  _  <- reserved "then"
  e2 <- parseExp
  _  <- reserved "else"
  e3 <- parseExp
  return $ IfExp e1 e2 e3

parseFun :: Parser Exp
parseFun = do
  _ <- reserved "fun"
  x <- identifier
  _ <- reservedOp "->"
  e <- parseExp
  return $ FunExp x e

parseLet :: Parser Exp
parseLet = do
  _    <- reserved "let"
  mrec <- optionMaybe $ reserved "rec" >> identifier
  name <- identifier
  _    <- reservedOp "="
  body <- parseExp
  _    <- reserved "in"
  e    <- parseExp
  return $ case mrec of
    Nothing -> LetInExp name body e
    Just f  -> LetRecInExp f name body e

parseNumber :: Parser Const
parseNumber = lexeme $ do
  integerPart <- many1 digit
  decimalPart <- optionMaybe (char '.' >> many digit)
  case decimalPart of
    Nothing -> return $ IntConst $ read integerPart
    Just d  -> return $ FloatConst $
                 read $ integerPart ++ "." ++ d ++ "0"
                 -- so we get 2.50, more importantly "2." => 2.0

parseString :: Parser Const
parseString = StringConst <$> stringLiteral

parseList :: Parser Exp
parseList = brackets $ desugar <$> parseListContents
  where
    parseListContents = sepBy parseAExp (reservedOp ";")
    desugar = foldr (\h t -> BinopExp h ConsOp t) (ConstExp NilConst)

--------------------------------------------------------------------------------------
--
-- Type-checking
--
--------------------------------------------------------------------------------------

------------------------------
-- Inferencing
------------------------------
type Infer a = WriterT [Constraint]
                 (ExceptT String
                 (State Int)) a
  -- exercise: when generating names, generate strings instead of ints.
  -- make TyVar hold a string.

type Constraint = (Monotype, Monotype)

runInfer :: Infer Monotype -> Either String Polytype
runInfer m = do
  (r, cs) <- evalState (runExceptT (runWriterT m)) 0
  s       <- solve cs
  return $ closeOver $ substMonotype s r

unify :: Monotype -> Monotype -> Infer ()
unify t1 t2 = tell [(t1, t2)]


infer :: Exp -> Gamma -> Infer Monotype

infer (ConstExp c) _ = instantiate $ signature c

infer (VarExp name) gamma = case lookupEnv gamma name of
  Just tau -> instantiate tau
  Nothing  -> throwError $ "variable name not in scope: " ++ name

infer (IfExp e1 e2 e3) gamma = do
  beta <- infer e1 gamma
  tau1 <- infer e2 gamma
  tau2 <- infer e3 gamma
  unify boolType beta
  unify tau1 tau2
  return tau1

infer (MonopExp m e) gamma = do
  tau1 <- infer e gamma
  tau  <- fresh
  sig  <- instantiate $ monopSignature m
  unify (tau1 `funType` tau) sig
  return tau
infer (BinopExp e1 b e2) gamma = do
  tau1 <- infer e1 gamma
  tau2 <- infer e2 gamma
  tau  <- fresh
  sig  <- instantiate $ binopSignature b
  unify (tau1 `funType` (tau2 `funType` tau)) sig
  return tau

infer (FunExp x e) gamma = do
  tau1 <- fresh
  tau2 <- infer e (insertEnv x (Forall [] tau1) gamma)
  return $ tau1 `funType` tau2

infer (AppExp f e) gamma = do
  tau1 <- infer f gamma
  tau2 <- infer e gamma
  tau3 <- fresh
  unify (tau2 `funType` tau3) tau1
  return tau3

infer (LetInExp x b e) gamma = do
  (taub, phi) <- listen $ infer b gamma
  subst       <- liftEither $ solve phi
  let taub' = generalize gamma $ substMonotype subst taub
  infer e (insertEnv x taub' gamma)

infer (LetRecInExp f x b e) gamma = do
  tau1        <- fresh
  tau2        <- fresh
  let tauf = tau1 `funType` tau2
  (tau3, phi) <- listen $ infer b
                 $ insertEnv x (Forall [] tau1) $ insertEnv f (Forall [] tauf) gamma
  subst       <- liftEither $ solve $ (tau2, tau3) : phi
  infer e $ insertEnv f (generalize gamma $ substMonotype subst tauf) gamma

inferTop e g = runInfer $ infer e g

------------------------------
-- Unifying
------------------------------

solve :: [Constraint] -> Either String Substitution
solve [] = return []
-- delete
solve ((t1,t2):rest)
  | t1 == t2 = solve rest
-- eliminate
solve ((TyVar n, mt):rest)
  | occursCheck n mt = throwError $
    "can't construct infinite type "
    ++ prettyType (TyVar n) ++ " ~ " ++ prettyType mt
  | otherwise = do
      phi <- solve rest'
      return $ (n, substMonotype phi mt) : phi
  where rest' = map substBoth rest
        substBoth (t1, t2) = (subst t1, subst t2)
        subst = substMonotype [(n,mt)]

        tvScope = n : S.toList (monotypeFvs mt)
        prettyType = prettyMonotypeWith tvScope
-- orient
solve ((mt, TyVar n):rest) = solve $ (TyVar n, mt) : rest
-- decompose
solve ((ta@(TyCon a as), tb@(TyCon b bs)):rest)
  | a == b = solve (zip as bs ++ rest)
  | otherwise = throwError $
    "Couldn't match expected type: " ++ prettyType ta ++
    "\n            with actual type: " ++ prettyType tb
  where
    tvScope = S.toList $ monotypeFvs ta `S.union` monotypeFvs tb
    prettyType = prettyMonotypeWith tvScope

occursCheck :: TyVar -> Monotype -> Bool
occursCheck ty mt = ty `S.member` monotypeFvs mt

------------------------------
-- Substitutions
------------------------------
type Substitution = [(TyVar, Monotype)]

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = mapSnd (substMonotype s1) s2 ++ s1
  where mapSnd f xs = map (\(a, b) -> (a, f b)) xs

delete :: TyVar -> Substitution -> Substitution
delete n [] = []
delete n ((v,m):s)
  | n == v    = s
  | otherwise = (v,m) : delete n s

substTyVar :: Substitution -> TyVar -> Monotype
substTyVar s n = case lookup n s of
  Nothing -> TyVar n
  Just mt -> mt

-- In a real program, we'd use a Substitutable typeclass here,
-- but I'm trying to keep this simple because we don't have
-- enough time this week to do all the type stuff and talk about
-- writing our own typeclasses.
substMonotype :: Substitution -> Monotype -> Monotype
substMonotype s (TyVar n) = substTyVar s n
substMonotype s (TyCon name tys) = TyCon name $ map (substMonotype s) tys

substPolytype :: Substitution -> Polytype -> Polytype
substPolytype s (Forall tys mt) = Forall tys $ substMonotype s' mt
  where s' = foldr delete s tys

substGamma :: Substitution -> Gamma -> Gamma
substGamma s g = map (\(n, ty) -> (n, substPolytype s ty)) g

------------------------------
-- free variables
------------------------------

monotypeFvs :: Monotype -> S.Set TyVar
monotypeFvs (TyCon _ tys) = S.unions $ map monotypeFvs tys
monotypeFvs (TyVar n) = S.singleton n

polytypeFvs :: Polytype -> S.Set TyVar
polytypeFvs (Forall tvs mt) = monotypeFvs mt `S.difference` S.fromList tvs

gammaFvs :: Gamma -> S.Set TyVar
gammaFvs env = S.unions $ map (polytypeFvs . snd) env

------------------------------
-- utilities
------------------------------

fresh :: Infer Monotype
fresh = do
  counter <- get
  put $ counter + 1
  return $ TyVar counter

-- turn monotype into polytype by quantifying the free variables
closeOver :: Monotype -> Polytype
closeOver = generalize []

generalize :: Gamma -> Monotype -> Polytype
generalize gamma mt = Forall tvs mt
  where tvs = S.toList $ monotypeFvs mt `S.difference` gammaFvs gamma

instantiate :: Polytype -> Infer Monotype
instantiate (Forall tvs mt) = do
  tvs' <- mapM (\_ -> fresh) tvs
  let s = zip tvs tvs'
  return $ substMonotype s mt

signature :: Const -> Polytype
signature IntConst{}    = Forall [] intType
signature FloatConst{}  = Forall [] floatType
signature BoolConst{}   = Forall [] boolType
signature StringConst{} = Forall [] stringType
signature UnitConst{}   = Forall [] unitType
signature NilConst{}    = Forall [0] $ listType $ TyVar 0

monopSignature :: Monop -> Polytype
monopSignature IntNegOp = Forall [] $ intType `funType` intType
monopSignature NotOp    = Forall [] $ boolType `funType` boolType

binopSignature :: Binop -> Polytype
binopSignature b = case b of
  intOp | intOp `elem` [IntPlusOp, IntSubOp, IntTimesOp, IntDivOp]
        -> binopType intType intType
  fltOp | fltOp `elem` [FloatPlusOp, FloatSubOp, FloatTimesOp, FloatDivOp]
        -> binopType floatType floatType
  cmpOp | cmpOp `elem` [EqOp, LtOp, LeqOp, GtOp, GeqOp]
        -> cmpBinopType
  ConsOp   -> consType
  StrCatOp -> binopType stringType stringType
  where
    binopType args res = Forall [] $ args `funType` (args `funType` res)
    cmpBinopType = Forall [0] $ var `funType` (var `funType` boolType)
    consType = Forall [0] $ var `funType` (listType var `funType` listType var)
    var = TyVar 0

intType    = TyCon "int" []
floatType  = TyCon "float" []
boolType   = TyCon "bool" []
stringType = TyCon "string" []
unitType   = TyCon "unit" []

listType tau = TyCon "list" [tau]
funType  tau1 tau2 = TyCon "->" [tau1, tau2]

--------------------------------------------------------------------------------------
--
-- Evaluate
--
--------------------------------------------------------------------------------------

evaluate :: Exp -> Sigma -> Val
evaluate (ConstExp c) env = case c of
  IntConst i    -> IntVal i
  FloatConst f  -> FloatVal f
  BoolConst b   -> BoolVal b
  StringConst s -> StringVal s
  UnitConst     -> UnitVal
  NilConst      -> ListVal []

evaluate (VarExp name) env = case lookupEnv env name of
  Nothing -> error "evaluate VarExp: not in env (impossible!)"
  Just v  -> v

evaluate (IfExp e1 e2 e3) env = case evaluate e1 env of
  BoolVal True  -> evaluate e2 env
  BoolVal False -> evaluate e3 env

evaluate (MonopExp m e) env = liftMonop m $ evaluate e env
evaluate (BinopExp e1 AndOp e2) env = case evaluate e1 env of
  BoolVal False -> BoolVal False
  _ -> evaluate e2 env
evaluate (BinopExp e1 OrOp e2) env = case evaluate e1 env of
  BoolVal True -> BoolVal True
  _ -> evaluate e2 env
evaluate (BinopExp e1 b e2) env =
  let v1 = evaluate e1 env
      v2 = evaluate e2 env
   in liftBinop b v1 v2

evaluate (FunExp x e) env = CloVal x e env
evaluate (AppExp f e) env =
  let CloVal x b envf = evaluate f env
      v1 = evaluate e env
   in evaluate b $ insertEnv x v1 envf

evaluate (LetInExp x b e) env =
  let v1 = evaluate b env
   in evaluate e $ insertEnv x v1 env

evaluate (LetRecInExp f x b e) env =
  let clo = CloVal x b $ insertEnv f clo env
   in evaluate e $ insertEnv f clo env

liftMonop :: Monop -> (Val -> Val)
liftMonop IntNegOp (IntVal i) = IntVal $ negate i
liftMonop NotOp (BoolVal b) = BoolVal $ not b

liftBinop :: Binop -> (Val -> Val -> Val)
liftBinop IntPlusOp  (IntVal x) (IntVal y) = IntVal $ x + y
liftBinop IntSubOp   (IntVal x) (IntVal y) = IntVal $ x - y
liftBinop IntTimesOp (IntVal x) (IntVal y) = IntVal $ x * y
liftBinop IntDivOp   (IntVal x) (IntVal y) = IntVal $ x `div` y

liftBinop FloatPlusOp  (FloatVal x) (FloatVal y) = FloatVal $ x + y
liftBinop FloatSubOp   (FloatVal x) (FloatVal y) = FloatVal $ x - y
liftBinop FloatTimesOp (FloatVal x) (FloatVal y) = FloatVal $ x * y
liftBinop FloatDivOp   (FloatVal x) (FloatVal y) = FloatVal $ x / y

liftBinop EqOp  v1 v2 = BoolVal $ v1 == v2
liftBinop LtOp  v1 v2 = BoolVal $ v1 <  v2
liftBinop LeqOp v1 v2 = BoolVal $ v1 <= v2
liftBinop GtOp  v1 v2 = BoolVal $ v1 > v2
liftBinop GeqOp v1 v2 = BoolVal $ v1 >= v2

liftBinop ConsOp v (ListVal vs) = ListVal (v:vs)
liftBinop StrCatOp (StringVal s1) (StringVal s2) = StringVal $ s1 ++ s2

--------------------------------------------------------------------------------------
--
-- Prettier Printing
--
--------------------------------------------------------------------------------------

prettyMonotypeWith :: [TyVar] -> Monotype -> String
prettyMonotypeWith vars = pretty
  where
    pretty ty = case ty of
      TyVar v        -> nameOf v
      TyCon name []  -> name
      TyCon name [t] -> unwords [pretty t, name]

      TyCon "->" [t1,t2] -> unwords [pretty t1, "->", pretty t2]
      TyCon name ts      -> "("
                              ++ intercalate " * " (map pretty ts)
                            ++ ") " ++ name

    nameOf = assocNames vars

prettyMonotype :: Monotype -> String
prettyMonotype t = prettyMonotypeWith (S.toList $ monotypeFvs t) t

prettyPolytype :: Polytype -> String
prettyPolytype (Forall [] t) = prettyMonotype t
prettyPolytype (Forall ts t) =
  "∀" ++ intercalate "," (map nameOf ts)
  ++ ". " ++ prettyMonotype t
  where
    nameOf = assocNames ts

typeNames :: [String]
typeNames = map ('\'':) $ [1..] >>= flip replicateM ['a'..'z']

assocNames :: [TyVar] -> (TyVar -> String)
assocNames vars = nameOf
  where
    nameAssocs = zip vars typeNames
    nameOf i = case lookup i nameAssocs of
      Nothing -> error "assocNames: bad visible type variable list"
      Just name -> name

prettyVal :: Val -> String
prettyVal v = case v of
  IntVal i      -> show i
  FloatVal d    -> show d
  BoolVal True  -> "true"
  BoolVal False -> "false"
  StringVal s   -> show s
  UnitVal       -> "()"
  ListVal vs    -> "[" ++ intercalate "; " (map prettyVal vs) ++ "]"
  CloVal{}      -> "<<closure>>"

--------------------------------------------------------------------------------------
--
-- REPL
--
--------------------------------------------------------------------------------------

replRead :: IO (Maybe Statement)
replRead = do
  putStr "λ> "
  line <- getLine
  case line of
    "quit" -> return Nothing
    _ -> let parseResult = parse line
         in case parseResult of
              Left pe    -> print pe >> replRead
              Right stmt -> return $ Just stmt

type Result = (Polytype, Val)
type TopEnvs = (Sigma, Gamma)

replEval :: Statement -> TopEnvs -> Either String (Result, TopEnvs)
replEval (AnonStmt e) envs@(sigma, gamma) =
  let mtau = inferTop e gamma
      v    = evaluate e sigma
  in case mtau of
      Left err -> Left err
      Right tau -> Right ((tau, v), envs)
replEval (LetStmt x e) (sigma, gamma) =
  let mtau = inferTop e gamma
      v    = evaluate e sigma
  in case mtau of
      Left err -> Left err
      Right tau -> let sigma' = insertEnv x v sigma
                       gamma' = insertEnv x tau gamma
                       envs' = (sigma', gamma')
                   in Right ((tau, v), envs')
replEval (LetRecStmt f x e) (sigma, gamma) =
  let mtau = inferTop (LetRecInExp f x e (VarExp f)) gamma
      v    = evaluate e sigma
  in case mtau of
      Left err -> Left err
      Right tau ->
        let clo = CloVal x e sigma'
            sigma' = insertEnv f clo sigma
            gamma' = insertEnv f tau gamma
            envs' = (sigma', gamma')
        in Right ((tau, clo), envs')

replPretty :: Either String Result -> String
replPretty (Left err) = err
replPretty (Right (ty, v)) = prettyVal v ++ " : " ++ prettyPolytype ty

replPrint :: Either String Result -> IO ()
replPrint = putStrLn . replPretty

repl :: TopEnvs -> IO ()
repl envs = do
  mstmt <- replRead
  case mstmt of
    Nothing -> return () -- done
    Just stmt -> case replEval stmt envs of
      Left err -> replPrint (Left err) >> repl envs
      Right (r, envs') -> replPrint (Right r) >> repl envs'

main = repl ([], [])

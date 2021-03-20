module Polytypes where

import Control.Applicative (liftA2)
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer

import Data.Functor (($>))
import qualified Data.Set as S

import Text.Parsec hiding (State, parse)
import qualified Text.Parsec as Parsec (parse)
import Text.Parsec.Language
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
  deriving (Eq, Show)

data Exp
  = ConstExp Const
  | VarExp   String
  | IfExp    Exp Exp Exp
  | ListExp  [Exp]
  deriving (Eq, Show)

data Const
  = IntConst    Integer
  | FloatConst  Double
  | BoolConst   Bool
  | StringConst String
  | UnitConst
  | NilConst
  deriving (Eq, Show)

data Monotype
  = TyConst String [Monotype]
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
  deriving (Eq, Show)

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
  { T.reservedOpNames = ["=", ";;"]
  , T.reservedNames =
    [ "true", "false"
    , "let"
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
  name <- identifier
  _    <- reservedOp "="
  body <- parseExp
  return $ LetStmt name body

parseAnonStmt :: Parser Statement
parseAnonStmt = AnonStmt <$> parseExp

parseExp :: Parser Exp
parseExp = ConstExp <$> parseConst
           <|> parseVar
           <|> parseIf
           <|> parens parseExp

parseConst :: Parser Const
parseConst = (reserved "true" $> BoolConst True)
             <|> (reserved "false" $> BoolConst False)
             <|> (parens (pure ()) $> UnitConst)
             <|> parseNumber
             <|> parseString
             <|> parseList

parseVar :: Parser Exp
parseVar = VarExp <$> identifier

parseIf :: Parser Exp
parseIf = do
  _  <- reserved "if"
  e1 <- parseExp
  _  <- reserved "then"
  e2 <- parseExp
  _  <- reserved "else"
  e3 <- parseExp
  return $ IfExp e1 e2 e3

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

parseList :: Parser Const
parseList = brackets (pure()) $> NilConst -- for now

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
runInfer m = case evalState (runExceptT (runWriterT m)) 0 of
  Left e  -> Left e
  Right (r, cs) -> case solve cs of
    Left e  -> Left e
    Right s -> Right $ closeOver s r

unify :: Monotype -> Monotype -> Infer ()
unify t1 t2 = tell [(t1, t2)]

-- Exp to infer, environment to infer in, and a "guess" for the type
-- of the expression, which is really just a type variable that will
-- be unified with the real type eventually.
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
    "can't construct infinite type " ++ show (TyVar n) ++ " ~ " ++ show mt
  | otherwise = do
      phi <- solve rest'
      return $ (n, substMonotype phi mt) : phi
  where rest' = map substBoth rest
        substBoth (t1, t2) = (subst t1, subst t2)
        subst = substMonotype [(n,mt)]
-- orient
solve ((mt, TyVar n):rest) = solve $ (TyVar n, mt) : rest
-- decompose
solve ((ta@(TyConst a as), tb@(TyConst b bs)):rest)
  | a == b = solve (zip as bs ++ rest)
  | otherwise = throwError $
    "Couldn't match expected type: " ++ show ta ++
    "\n            with actual type: " ++ show tb

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
substMonotype s (TyConst name tys) = TyConst name $ map (substMonotype s) tys

substPolytype :: Substitution -> Polytype -> Polytype
substPolytype s (Forall tys mt) = Forall tys $ substMonotype s' mt
  where s' = foldr delete s tys

substGamma :: Substitution -> Gamma -> Gamma
substGamma s g = map (\(n, ty) -> (n, substPolytype s ty)) g

------------------------------
-- free variables
------------------------------

monotypeFvs :: Monotype -> S.Set TyVar
monotypeFvs (TyConst _ tys) = S.unions $ map monotypeFvs tys
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
closeOver :: Substitution -> Monotype -> Polytype
closeOver s mt = generalize [] (substMonotype s mt)

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
signature NilConst{}    = Forall [0] $ TyConst "[]" [TyVar 0]

intType    = TyConst "int" []
floatType  = TyConst "float" []
boolType   = TyConst "bool" []
stringType = TyConst "string" []
unitType   = TyConst "unit" []

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

replPretty :: Either String Result -> String
replPretty (Left err) = err
replPretty (Right (ty, v)) = show v ++ " : " ++ show ty

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

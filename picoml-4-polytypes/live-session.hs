{-
This file contains the starting point code for the live session.
It contains a bunch of utility functions and a couple type definitions
that were not present in Conditionals.hs, but is missing the rest of the
life code for the Polytypes.hs file.
-}
module Polytypes where

import Control.Applicative (liftA2)

import Data.Functor (($>))
import Data.List (intercalate)

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
  = TyCon String [Monotype]
  deriving (Eq, Show)

data Val
  = IntVal    Integer
  | FloatVal  Double
  | BoolVal   Bool
  | StringVal String
  | UnitVal
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

--------------------------------------------------------------------------------------
--
-- Type-checking
--
--------------------------------------------------------------------------------------

------------------------------
-- Inferencing
------------------------------

------------------------------
-- Unifying
------------------------------

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
closeOver mt = generalize [] mt

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
signature NilConst{}    = Forall [0] $ TyCon "list" [TyVar 0]

intType    = TyCon "int" []
floatType  = TyCon "float" []
boolType   = TyCon "bool" []
stringType = TyCon "string" []
unitType   = TyCon "unit" []

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

evaluate (VarExp name) env = case lookupEnv env name of
  Nothing -> error "evaluate VarExp: not in env (impossible!)"
  Just v  -> v

evaluate (IfExp e1 e2 e3) env = case evaluate e1 env of
  BoolVal True  -> evaluate e2 env
  BoolVal False -> evaluate e3 env

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
  let mtau = typecheck e gamma
      v    = evaluate e sigma
  in case mtau of
      Left err -> Left err
      Right tau -> Right ((tau, v), envs)
replEval (LetStmt x e) (sigma, gamma) =
  let mtau = typecheck e gamma
      v    = evaluate e sigma
  in case mtau of
      Left err -> Left err
      Right tau -> let sigma' = insertEnv x v sigma
                       gamma' = insertEnv x tau gamma
                       envs' = (sigma', gamma')
                   in Right ((tau, v), envs')

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

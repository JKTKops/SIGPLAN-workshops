module ConstantsOnly where

import Control.Applicative (liftA2)
import Data.Functor (($>))
import Text.Parsec hiding (parse)
import qualified Text.Parsec as Parsec (parse)
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
  | VarExp String
  deriving (Eq, Show)

data Const
  = IntConst   Integer
  | FloatConst Double
  | BoolConst  Bool
  | UnitConst
  -- add StringConst if we have time, harder to parse
  -- leave off NilConst (and SAY we're leaving it off)
  --   because typechecking it requires tyvars
  deriving (Eq, Show)

data Type
  = TyConst String
  deriving (Eq, Show)

data Val
  = IntVal Integer
  | FloatVal Double
  | BoolVal  Bool
  | UnitVal
  deriving (Eq, Show)

--------------------------------------------------------------------------------------
--
-- Utilities
--
--------------------------------------------------------------------------------------

type Env a = [(String, a)]
type Gamma = Env Type
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

-- this will evolve as we add to the interpreter
parse :: String -> Either ParseError Statement
parse = Parsec.parse parseStmt "<interactive>"

parseStmt :: Parser Statement
parseStmt = do
  stmt <- parseLetStmt <|> parseAnonStmt
  _    <- string ";;"
  return stmt

parseLetStmt :: Parser Statement
parseLetStmt = do
  _    <- try $ string "let"
  _    <- spaces
  name <- parseName
  _    <- between spaces spaces $ char '='
  body <- parseExp
  return $ LetStmt name body

parseAnonStmt :: Parser Statement
parseAnonStmt = AnonStmt <$> parseExp

parseName :: Parser String
parseName = liftA2 (:) letter (many alphaNum)

parseExp :: Parser Exp
parseExp = ConstExp <$> parseConst
           <|> parseVar

parseConst :: Parser Const
parseConst = (string "true" $> BoolConst True)
             <|> (string "false" $> BoolConst False)
             <|> (string "()" $> UnitConst)
             <|> parseNumber

parseVar :: Parser Exp
parseVar = VarExp <$> parseName

parseNumber :: Parser Const
parseNumber = do
  integerPart <- many1 digit
  decimalPart <- optionMaybe (char '.' >> many digit)
  case decimalPart of
    Nothing -> return $ IntConst $ read integerPart
    Just d  -> return $ FloatConst $
                 read $ integerPart ++ "." ++ d ++ "0"
                 -- so we get 2.50, more importantly "2." => 2.0

--------------------------------------------------------------------------------------
--
-- Type-checking
--
--------------------------------------------------------------------------------------

-- this section will get much more involved in the future, for now there's
-- almost nothing to do.

typecheck :: Exp -> Gamma -> Maybe Type
typecheck (ConstExp c) _ = Just $ TyConst $ case c of
  IntConst{}   -> "int"
  FloatConst{} -> "float"
  BoolConst{}  -> "bool"
  UnitConst{}  -> "unit"
typecheck (VarExp name) gamma = lookupEnv gamma name

--------------------------------------------------------------------------------------
--
-- Evaluate
--
--------------------------------------------------------------------------------------


evaluate :: Exp -> Sigma -> Val
evaluate (ConstExp c) env = case c of
  IntConst i   -> IntVal i
  FloatConst f -> FloatVal f
  BoolConst b  -> BoolVal b
  UnitConst    -> UnitVal
evaluate (VarExp name) env = case lookupEnv env name of
  Nothing -> error "evaluate VarExp: not in env (impossible!)"
  Just v  -> v

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

type Result = (Type, Val)
type TopEnvs = (Sigma, Gamma)

replEval :: Statement -> TopEnvs -> Maybe (Result, TopEnvs)
replEval (AnonStmt e) envs@(sigma, gamma) =
  let mtau = typecheck e gamma
      v    = evaluate e sigma
  in case mtau of
      Nothing  -> Nothing
      Just tau -> Just ((tau, v), envs)
replEval (LetStmt x e) (sigma, gamma) =
  let mtau = typecheck e gamma
      v   = evaluate e sigma
  in case mtau of
      Nothing -> Nothing
      Just tau -> let sigma' = insertEnv x v sigma
                      gamma' = insertEnv x tau gamma
                      envs' = (sigma', gamma')
                  in Just ((tau, v), envs')

replPretty :: Maybe Result -> String
replPretty Nothing = "did not typecheck"
replPretty (Just (ty, v)) = show v ++ " : " ++ show ty

replPrint :: Maybe Result -> IO ()
replPrint = putStrLn . replPretty

repl :: TopEnvs -> IO ()
repl envs = do
  mstmt <- replRead
  case mstmt of
    Nothing -> return () -- done
    Just stmt -> case replEval stmt envs of
      Nothing -> replPrint Nothing >> repl envs
      Just (r, envs') -> replPrint (Just r) >> repl envs'

main = repl ([], [])

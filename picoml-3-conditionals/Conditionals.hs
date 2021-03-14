module Conditionals where

import Control.Applicative (liftA2)
import Data.Functor (($>))
import Text.Parsec hiding (parse)
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
  -- leave off NilConst (and SAY we're leaving it off)
  --   because typechecking it requires tyvars
  deriving (Eq, Show)

data Type
  = TyConst String
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

picomlDef :: LanguageDef st
picomlDef = emptyDef
  { T.commentStart = "(*"
  , T.commentEnd   = "*)"
  , T.reservedOpNames = ["=", ";;"]
  , T.reservedNames =
    [ "true", "false"
    , "let"
    , "if", "else", "then"
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
parse = Parsec.parse (between whitespace eof parseStmt) "<interactive>"

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
           <|> parens parseExp -- eventually parens parseAExp!

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
                 -- Parsec's 'float' parser doesn't do this, so we
                 -- will keep doing it ourselves.

parseString :: Parser Const
parseString = StringConst <$> stringLiteral

--------------------------------------------------------------------------------------
--
-- Type-checking
--
--------------------------------------------------------------------------------------

-- this section will get much more involved in the future, for now there's
-- almost nothing to do.

typecheck :: Exp -> Gamma -> Maybe Type
typecheck (ConstExp c) _      = Just $ typeof c
typecheck (VarExp name) gamma = lookupEnv gamma name
typecheck (IfExp e1 e2 e3) gamma = do
  t1 <- typecheck e1 gamma
  tau1 <- typecheck e2 gamma
  tau2 <- typecheck e3 gamma
  case t1 of
    TyConst "bool"
      | tau1 == tau2 -> Just tau1
    _ -> Nothing

typeof :: Const -> Type
typeof IntConst{}    = TyConst "int"
typeof FloatConst{}  = TyConst "float"
typeof BoolConst{}   = TyConst "bool"
typeof StringConst{} = TyConst "string"
typeof UnitConst{}   = TyConst "unit"

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

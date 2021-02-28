module ConstantsOnly where

import Data.Functor (($>))
import Text.Parsec hiding (parse)
import qualified Text.Parsec as Parsec (parse)
import Text.Parsec.String

--------------------------------------------------------------------------------------
--
-- Data Types
--
--------------------------------------------------------------------------------------

data Exp
  = ConstExp Const
  deriving (Eq, Show)

data Const
  = IntConst   Integer
  | FloatConst Double
  | BoolConst  Bool
  | StringConst String
  | UnitConst
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
  | StringVal String
  | UnitVal
  deriving (Eq, Show)

--------------------------------------------------------------------------------------
--
-- Parsing
--
--------------------------------------------------------------------------------------

-- this will evolve as we add to the interpreter
parse :: String -> Either ParseError Exp
parse = Parsec.parse parseExp "<interactive>"

parseExp :: Parser Exp
parseExp = ConstExp <$> parseConst
  -- (<$>) :: (a -> b) -> (Parser a -> Parser b)

parseConst :: Parser Const
parseConst = (string "true" $> BoolConst True)
             <|> (string "false" $> BoolConst False)
             <|> (string "()" $> UnitConst)
             <|> parseNumber
             <|> parseString

parseNumber :: Parser Const
parseNumber = do
  integerPart <- many1 digit
  decimalPart <- optionMaybe (char '.' >> many digit)
  case decimalPart of
    Nothing -> return $ IntConst $ read integerPart
    Just d  -> return $ FloatConst $
                 read $ integerPart ++ "." ++ d ++ "0"
                 -- so we get 2.50, more importantly "2." => 2.0

parseString :: Parser Const
parseString = StringConst <$> between (char '"') (char '"') parseStringContents

parseStringContents :: Parser String
parseStringContents = many $ noneOf ['"', '\\'] <|> parseEscapeChar
  where
    parseEscapeChar = do
      character <- char '\\' >> oneOf ['"', '\\', 't']
      return $ case character of
        '"' -> '"'
        '\\' -> '\\'
        't'  -> '\t'

--------------------------------------------------------------------------------------
--
-- Type-checking
--
--------------------------------------------------------------------------------------

-- this section will get much more involved in the future, for now there's
-- almost nothing to do.

typecheck :: Exp -> Type
typecheck (ConstExp c) = typeof c

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

evaluate :: Exp -> Val
evaluate (ConstExp c) = case c of
    IntConst i    -> IntVal i
    FloatConst f  -> FloatVal f
    BoolConst b   -> BoolVal b
    UnitConst     -> UnitVal
    StringConst s -> StringVal s

--------------------------------------------------------------------------------------
--
-- REPL
--
--------------------------------------------------------------------------------------

replRead :: IO (Maybe Exp)
replRead = do
  putStr "λ> "
  line <- getLine
  case line of
    "quit" -> return Nothing
    _ -> let parseResult = parse line
         in case parseResult of
              Left pe -> print pe >> replRead
              Right exp -> return $ Just exp

type Result = (Type, Val)

replEval :: Exp -> Result
replEval e = (typecheck e, evaluate e)

-- we will improve on this in the future / now if we have time
replPretty :: Result -> String
replPretty (ty, v) = show v ++ " : " ++ show ty

repl :: IO ()
repl = do
  mexp <- replRead
  case mexp of
    Nothing -> return () -- done
    Just e  -> do
      putStrLn $ replPretty $ replEval e
      repl

main = repl

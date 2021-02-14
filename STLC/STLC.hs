module STLC where

import Data.Maybe (fromJust)

-- for the parser
import Data.Functor (($>))
import Text.Parsec hiding (parse)
import Text.Parsec.Char (char)
import Text.Parsec.Combinator (between)
import Text.Parsec.String (Parser)

-- for the repl
import System.IO (hFlush, stdout)

data Exp
  = Lam ExEnv (String, Type) Exp
    -- Lam (String, Type) Exp
  | App Exp Exp
  | Var String
  | Unit
  deriving Show

data Type
  = UnitTy
  | Type :-> Type
  deriving (Eq, Show)

type Env a = [(String, a)]
type TyEnv = Env Type
type ExEnv = Env Exp

lookupEnv :: Env a -> String -> Maybe a
lookupEnv [] _ = Nothing
lookupEnv ((name, thing) : rest) desire
  | name == desire = Just thing
  | otherwise      = lookupEnv rest desire

check :: TyEnv -> Exp -> Maybe Type
check _   Unit       = Just UnitTy
check env (Var name) = lookupEnv env name
check env (Lam _{- <- don't include before closures -}
             binding@(_,σ) term) = case (binding:env) ⊢ term of
  Nothing -> Nothing
  Just τ  -> Just (σ :-> τ)
check env (App f x) = case env ⊢ f of
  Nothing -> Nothing
  Just (σ :-> τ) -> case env ⊢ x of
    Nothing -> Nothing
    Just σ'
      | σ == σ'   -> Just τ
      | otherwise -> Nothing
  Just _ -> Nothing

(⊢) = check

interp :: Exp -> Maybe (Exp, Type)
interp exp = case check [] exp of
  Nothing -> Nothing
  Just ty -> Just (interp' exp [], ty)
  where
    interp' Unit env = Unit
    interp' (Var name) env = fromJust (lookupEnv env name)
    interp' (Lam _ binding body) env = Lam env binding body
    -- interp' term@Lam{} = term
    interp' (App f x) env = case interp' f env of
      Lam clenv (name, _) body ->
        interp' body ((name, interp' x env):clenv++env)

--------------------------------------------------------------------------------------
--
-- parser
--
--------------------------------------------------------------------------------------


parse :: String -> Either ParseError Exp
parse = runParser parseAExp () "<interactive>"

parens :: Parser a -> Parser a
parens = between (char '(') (char ')')

-- the interested reader could look at the Parsec documentation and try to
-- allow the parser to accept whitespace
parseType :: Parser Type
parseType = chainr1 (parseUnitTy <|> parens parseType) functionArrow
  where functionArrow = string "->" $> (:->)

parseUnitTy :: Parser Type
parseUnitTy = char 'I' $> UnitTy

parseAExp :: Parser Exp
parseAExp = chainl1 (parseExp <|> parens parseAExp) application
  where application = spaces $> App

parseExp :: Parser Exp
parseExp = parseUnit <|> parseLam <|> parseVar

parseUnit :: Parser Exp
parseUnit = char 'i' $> Unit

parseLam :: Parser Exp
parseLam = do
    _    <- char '\\' <|> char 'λ'
    name <- many1 letter
    _    <- char ':'
    ty   <- parseType
    _    <- char '.'
    body <- parseAExp
    return $ Lam [] (name, ty) body

parseVar :: Parser Exp
parseVar = Var <$> many1 letter

--------------------------------------------------------------------------------------
--
-- REPL
--
--------------------------------------------------------------------------------------

replRead :: IO (Maybe Exp)
replRead = do
    putStr "λ> "
    hFlush stdout
    line <- getLine
    case line of
        "quit" -> return Nothing
        _ -> case parse line of
            Left pe -> print pe >> replRead
            Right exp -> return $ Just exp

-- the interested reader could add better error messages
-- or look into how to define nicer "show" instances.
replEval :: Exp -> IO ()
replEval exp = case interp exp of
    Nothing -> putStrLn "couldn't interpret that."
    Just (r,t) -> print r >> print t

repl :: IO ()
repl = do
    mexp <- replRead
    case mexp of
        Nothing -> pure ()
        Just exp -> replEval exp >> repl

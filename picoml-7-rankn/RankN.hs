-- To add RankN types, I follow along the paper
-- "Practical Type Inference For Arbitrary-Rank Types," by
-- Jones, Vytiniotis, Weirich, Shields
-- The existing algorithm implemented in the previous iterations
-- of these playgrounds used offline unification, but this algorithm
-- (apparently) requires online unification to work.
{-# LANGUAGE LambdaCase #-}
module RankN where

import Control.Applicative (liftA2)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.ST
-- We only have IO in our monad stack for access to Refs. We'd
-- use ST instead of IO if it were a simple choice in a vacuum. But
-- types can contain these type variable refs, and expressions can
-- contain types, and the state thread ends up infecting everything.
-- Of course, there are ways to dodge this (a version of Type with
-- no MetaTvs to be used in the AST would help) but it's generally
-- annoying. Instead we use IO under the hood and keep it to mutation.
import Control.Monad.ST.Unsafe (unsafeIOToST)
import Control.Monad.Writer

import Data.Functor (($>), (<&>))
import Data.List (intercalate)
import Data.Set qualified as S
import Data.Map qualified as M
import Data.Maybe
import Data.IORef

import Text.Parsec hiding (State, parse)
import Text.Parsec qualified as Parsec (parse)
import Text.Parsec.Language
import Text.Parsec.Expr
import Text.Parsec.Token qualified as T
import Text.Parsec.String

import Debug.Trace
import Data.Either (fromRight)

--------------------------------------------------------------------------------------
--
-- Language Data Types
--
--------------------------------------------------------------------------------------

data Statement
  = AnonStmt Exp  -- e;;
  | LetStmt  String (Maybe SigmaType) Exp          -- let x {:s} = e;;
  | LetRecStmt String String (Maybe SigmaType) Exp -- let rec (f {:s}) x = e;;
                                                   -- parens optional if no annotation
  | TypeStmt Signature
  deriving (Eq, Show)

-- For now, we're only passing these around in TypeStmt,
-- so we could unpack it directly into TypeStmt.
-- However, if we were to add a coverage checker to our
-- interpreter, we'd need to properly pass around
-- Signatures as they are created.
data Signature = Sig [String] String [ConDecl]
  deriving (Eq, Show)

data Exp
  = ConstExp Const
  | VarExp   String
  | IfExp    Exp Exp Exp
  | TupleExp [Exp] -- must have 2+ elements in the list
  | ListExp  [Exp]
  | MonopExp Monop Exp
  | BinopExp Exp Binop Exp
  | FunExp   String (Maybe SigmaType) Exp
  | AppExp   Exp Exp
  | LetInExp String Exp Exp
  | LetRecInExp String String Exp Exp
  | MatchExp Exp [MatchCase]
  | AnnExp Exp SigmaType -- e : s
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

-- Another thing we could add later: case guards.
-- That is, another (optional) Exp, which must evaluate to a boolean,
-- (but which has access to the pattern variables)
-- and the pattern match only succeeds if the boolean is true.
data MatchCase = MC { casePat :: Pattern, caseExp :: Exp }
  deriving (Eq, Ord, Show)

-- This type has four "cases." Firstly, notice that we use String
-- instead of UniqueName. It's not the Pattern's job to know _which_
-- constructor of this name is referred to. Of course, a compiler
-- would probably want to figure that out, but our interpreter can
-- pretend it's not a problem. As long as we make sure it's the correct
-- one during type checking, the evaluator can ignore it. So we'll
-- have to lookup the constructor when we do typechecking.
--
-- Pat "Foo" []                       ==> Foo
-- Pat "Foo" [PatVar "t"]             ==> Foo t
-- Pat "Foo" [PatVar "t", PatVar "s"] ==> Foo (t, s)
-- Pat "*"   [PatVar "t", ...]        ==> (t, ...) 
--
-- These four cases have fairly different typing semantics,
-- the last one especially.
data Pattern = Pat String [PatternVar]
  deriving (Eq, Ord, Show)

data PatternVar = VarPat String | Wildcard
  deriving (Eq, Ord, Show)

data Type
  = Arrow Type Type
  | TyCon UniqueName [Type]
  | TyVar TyVar
  | MetaTv MetaTv
  | Forall [TyVar] Type
  deriving (Eq, Ord, Show)

type TauType = Type -- no foralls at all
type RhoType = Type -- no forall at the top
type SigmaType = Type

data UniqueName = UniqueName Int String -- int will be 0 for builtin, >= 1 for user
                -- however, the parser always outputs 0, and it will be fixed in exec
                -- before adding anything to the environment
  deriving (Show)
instance Eq UniqueName where
  UniqueName 0 s1 == UniqueName 0 s2 = s1 == s2
  UniqueName n1 _ == UniqueName n2 _ = n1 == n2
instance Ord UniqueName where
  UniqueName n1 _ `compare` UniqueName n2 _ = n1 `compare` n2

data ConDecl = ConDecl UniqueName (Maybe Type)
  -- ConDecl Name Nothing                           ===>     | Name
  -- ConDecl Name (Just (TyVar ...))                ===>     | Name of 'a
  -- ConDecl Name (Just (TyCon tupleType [f1,...])) ===>     | Name of f1 * ...
  -- Syntactically these cases are different, but semantically the only separation
  -- is between the first case and the other two. Either the constructor is nullary,
  -- or it takes one argument, which might be a tuple.
  deriving (Eq, Show)

builtinName :: String -> UniqueName
builtinName = UniqueName 0

-- type variables written by the user
data TyVar = BoundTv String | SkolemTv UniqueName
  deriving (Eq, Ord, Show)

-- type variables generated by inference
type MvRef = IORef (Maybe TauType)
data MetaTv = Meta Int MvRef
instance Eq MetaTv where
  Meta n1 _ == Meta n2 _ = n1 == n2
instance Ord MetaTv where
  Meta n1 _ `compare` Meta n2 _ = n1 `compare` n2
instance Show MetaTv where
  show (Meta n _) = show n

tvName :: TyVar -> String
tvName (BoundTv n) = n
tvName (SkolemTv (UniqueName _ n)) = n

data Val
  = IntVal    Integer
  | FloatVal  Double
  | BoolVal   Bool
  | StringVal String
  | UnitVal
  | TupleVal [Val] -- list must contain at least 2 things

    -- For user-defined values, we have a choice:
    --  1) behave like OCaml: non-nullary constructors cannot appear without an argument
    --  2) behave like Haskell: non-nullary constructors written without an argument
    --      are a function of type [arg type] -> [constructor's signature's type]
    --
    -- In the first case, we have to detect & reject bad programs. In the second
    -- case, we have to introduce a couple of simple evaluation rules. So we'll
    -- go with the second option. But this is a choice!
    -- To implement all this, we use this UserVal constructor.
    -- This serves a double purpose; data constructor values that should take
    -- no arguments are represented as UserVal <name> Nothing.
    -- Data constructor values that expect one argument, but are not (yet)
    -- applied, are represented the same. Applied data constructors are
    -- represented as UserVal <name> (Just v). There can only ever be one
    -- argument; it might be a tuple.
  | UserVal UniqueName (Maybe Val)
  | CloVal String Exp Sigma
  deriving (Eq, Ord, Show)

--------------------------------------------------------------------------------------
--
-- Utilities
--
--------------------------------------------------------------------------------------

type Env a = [(String, a)]
type Gamma = Env SigmaType
type Sigma = Env Val -- slightly confusing name for evaluation environment.
                     -- Nothing to do with SigmaType!
type Delta = Env Signature -- stack of type declarations (newest first)

lookupEnv :: Env a -> String -> Maybe a
lookupEnv = flip lookup -- talk about combinators again

insertEnv :: String -> a -> Env a -> Env a
insertEnv s a env = (s,a):env

unionEnv :: Env a -> Env a -> Env a
unionEnv = (++)

cleanWildcards :: (a -> b) -> [(PatternVar, a)] -> Env b
cleanWildcards f = concatMap one where
  one (VarPat name, a) = [(name, f a)]
  one (Wildcard, _) = []

--------------------------------------------------------------------------------------
--
-- Parsing
--
--------------------------------------------------------------------------------------

picomlDef :: LanguageDef st
picomlDef = emptyDef
  { T.reservedOpNames =
    [ "=", "->", ";;", "|", ","
    , "+", "-", "*", "/"
    , "+.", "-.", "*.", "/."
    , "<", ">", "<=", ">="
    , ".", ":", "::" -- type annotations, cons
    , "&&", "||"
    , "^"
    ]
  , T.reservedNames =
    [ "true", "false"
    , "let", "rec", "in"
    , "if", "then", "else"
    , "type", "of"
    , "match", "with", "_"
    , "forall"
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

typeIdentifier :: Parser String
typeIdentifier = char '\'' >> identifier

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
  stmt <- parseLetStmt <|> parseAnonStmt <|> parseTypeStmt
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
      Nothing -> LetStmt name Nothing body
      Just f  -> LetRecStmt f name Nothing body
    Just e -> case mrec of
      Nothing -> AnonStmt $ LetInExp name body e
      Just f  -> AnonStmt $ LetRecInExp f name body e

parseAnonStmt :: Parser Statement
parseAnonStmt = AnonStmt <$> parseExp

parseExp :: Parser Exp
parseExp = flip (<?>) "expression" $ do
  me <- parseMainExp
  optTy <- optionMaybe (reservedOp ":" *> parseType)
  return $ maybe me (AnnExp me) optTy
  where
    parseMainExp =
          parseIf
      <|> parseFun
      <|> parseLet
      <|> parseMatch
      <|> parseOpExp

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
                 <|> parenThing
                 <|> parseList
                 <?> "value expression"
  where
    parenThing = do
      lst <- parens $ parseExp `sepBy` reservedOp ","
      return $ case lst of
        []  -> ConstExp UnitConst
        [e] -> e
        es  -> TupleExp es

parseConst :: Parser Const
parseConst = (reserved "true" $> BoolConst True)
             <|> (reserved "false" $> BoolConst False)
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
  return $ FunExp x Nothing e

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

parseMatch :: Parser Exp
parseMatch = do
  _     <- reserved "match"
  scrut <- parseExp -- "scrutinee" is the technical term
  _     <- reserved "with"
  cases <- many1 (reservedOp "|" >> parseCase)
  return $ MatchExp scrut cases

parseCase :: Parser MatchCase
parseCase = do
  pat   <- parsePat
  _     <- reservedOp "->"
  exp   <- parseExp
  return $ MC { casePat = pat, caseExp = exp }

parsePat :: Parser Pattern
parsePat = try listPat
       <|> parenPat
       <|> (Pat <$> identifier <*> constrArgs) where
  constrArgs = tupleArgs <|> oneArg <|> noArgs
  noArgs = pure []
  oneArg = singleton <$> patVar
  tupleArgs = parens $ patVar `sepBy1` reservedOp ","
  singleton x = [x]

  listPat = nilPat <|> consPat
  nilPat = brackets $ pure $ Pat "[]" []
  consPat = do
    hd <- patVar
    _  <- reservedOp "::"
    tl <- patVar
    return $ Pat "::" [hd, tl]

  parenPat = parens (patVar `sepBy` reservedOp ",") >>= processParenPat 
  processParenPat []  = return $ Pat "()" []
  processParenPat [v] = unexpected "(<pat-var>) (this is not allowed)"
  processParenPat vs  = return $ Pat "*" vs

  patVar = (reserved "_" $> Wildcard) <|> (VarPat <$> identifier)

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
parseList = brackets $ ListExp <$> parseListContents
  where
    parseListContents = sepBy parseAExp (reservedOp ";")

parseTypeStmt :: Parser Statement
parseTypeStmt = do
  _    <- reserved "type"
  as   <- fmap singleton typeIdentifier  -- type { 'a } name ...
          <|> parens (typeIdentifier `sepBy1` reservedOp ",") -- type { ('a,...) } name ...
          <|> pure [] -- type name ...
  name <- identifier -- type TyVars { name } ...
  _    <- reservedOp "="
  cs   <- parseConDecl `sepBy1` reservedOp "|" -- rejects type name = | C1 | C2 | ...
                                               -- because of this:    ^
                                               -- but that's OK. write type name = C1 | C2 | ...
  return $ TypeStmt $ Sig as name cs
  where singleton x = [x]

parseConDecl :: Parser ConDecl
parseConDecl = do
  n <- identifier
  t <- optionMaybe $ reserved "of" *> parseTypeInside
  -- create a builtin name for the constructor. In order to "execute" a
  -- TypeStmt, we'll need to assign a fresh number to the signature
  -- (that is, the name of the type and all of its constructors) of
  -- the TypeStmt. This number will disambiguate among types that
  -- shadow each other. But we can't do it yet, because we don't know
  -- in the parser how many other type names we've read. In a real compiler,
  -- we have the same problem: this disambiguation is a _semantic_ analysis,
  -- not a _syntactic_ analysis.
  return $ ConDecl (UniqueName 0 n) t

parseType :: Parser Type
parseType = do
  t <- parseTypeInside
  checkClosed t
  return t

checkClosed :: Type -> Parser ()
checkClosed t
  | null ftvs = pure ()
  | otherwise = fail $ "Unbound type variable: '" ++ tvName ex
  where
    ftvs = freeTyVars t
    ex = head $ S.toList ftvs

parseTypeInside :: Parser Type
parseTypeInside = parseForallType <|> parseArrowType
  where
    parseForallType = do
      _ <- reserved "forall"
      tvs <- map BoundTv <$> many1 typeIdentifier
      _ <- reservedOp "."
      -- use ArrowType to disallow forall 'a. forall 'b. ...
      -- must be written forall 'a 'b. ...
      Forall tvs <$> parseArrowType

parseArrowType :: Parser Type
parseArrowType = chainr1 parseProdType (reservedOp "->" $> Arrow)

parseProdType :: Parser Type
parseProdType = do
  -- parse many ATypes separated by '*'s. This weird way of doing that
  -- avoids a particular problem common to recursive grammars that would
  -- otherwise lead to an infinite loop. 'chainr1' is specially designed
  -- to work around this. 'chainr1' also fails if it isn't able to parse
  -- at least one AType, so we can assume that 'lst' is nonempty.
  lst <- chainr1 (fmap singleton parseAType) (reservedOp "*" $> (++))
  return $ case lst of
    [t] -> t
    ts  -> TyCon (builtinName "*") ts

singleton :: a -> [a]
singleton x = [x]

parseAType :: Parser Type
parseAType = do
  ps <- parseTypeParams -- tyvar, or nullary tycon, or (ty, ...) [possibly only 1]
  conNames <- case ps of
    -- we'll figure out what the numbers are supposed to be later
    (_:_:_) -> many1 $ UniqueName 0 <$> identifier  -- 2+ type params; constructor required
    _       -> many  $ UniqueName 0 <$> identifier  -- <2 type params; might be solo type [like 'a or (int)]
  return $ assembleAType conNames ps
  where
    assembleAType [] [t] = t -- solo type
    assembleAType [n] ts = TyCon n ts -- constructor with ts as type arguments
    assembleAType (n:ns) ts = assembleAType ns [TyCon n ts] -- nested constructors (e.g. int list option)

parseTypeParams :: Parser [Type]
parseTypeParams =
    (singleton . TyVar . BoundTv <$> typeIdentifier)
    <|> (singleton . conOf <$> identifier)
    <|> parens (parseTypeInside `sepBy1` reserved ",")
  where
    conOf name = TyCon (UniqueName 0 name) []

--------------------------------------------------------------------------------------
--
-- Type-checking
--
--------------------------------------------------------------------------------------

-- Rename types according to given scope
renameType :: Uniques -> Type -> Either String Type
renameType u = go where
  go t@MetaTv{} = pure t
  go t@TyVar{}  = pure t
  go (Arrow t1 t2) = Arrow <$> go t1 <*> go t2
  -- boundvar names here must start with ' still so there's no risk
  -- of shadowing a type constructor name.
  go (Forall tvs t) = Forall tvs <$> go t
  go (TyCon (UniqueName 0 n) ts) = do
    uniq <- case u M.!? n of
      Nothing -> throwError $ "Unbound type constructor: " ++ n
      Just uniq -> return uniq
    TyCon (UniqueName uniq n) <$> mapM go ts

renameTypesInExp :: Uniques -> Exp -> Either String Exp
renameTypesInExp uniqs = go where
  go e@(ConstExp{})        = pure e
  go e@(VarExp{})          = pure e
  go (AppExp e1 e2)        = AppExp <$> go e1 <*> go e2
  go (IfExp c t f)         = IfExp <$> go c <*> go t <*> go f
  go (FunExp x Nothing b)  = FunExp x Nothing <$> go b
  go (FunExp x (Just t) b) = FunExp x <$> (Just <$> renameType uniqs t) <*> go b
  go (ListExp es)          = ListExp <$> mapM go es
  go (TupleExp es)         = TupleExp <$> mapM go es
  go (MonopExp op e)       = MonopExp op <$> go e
  go (BinopExp x op y)     = BinopExp <$> go x <*> pure op <*> go y
  go (LetInExp x e b)      = LetInExp x <$> go e <*> go b
  go (LetRecInExp f x e b) = LetRecInExp f x <$> go e <*> go b
  go (MatchExp scr cases)  = MatchExp <$> go scr <*> mapM goMC cases
  go (AnnExp e ty)         = AnnExp <$> go e <*> renameType uniqs ty

  goMC (MC pat arm)        = MC pat <$> go arm

------------------------------
-- Monad
------------------------------
data IEnv = IEnv { supply :: IORef Int, env :: Gamma }

type Infer a =
  (ReaderT IEnv
    (ExceptT String
    IO) a)

data Expected t
  = Check t
  | Infer (IORef t)

runInfer :: Infer a -> Gamma -> Either String a
runInfer m g = runST $ unsafeIOToST $ do
    ctr <- newIORef 0
    runExceptT (runReaderT m (IEnv ctr g))

newInfer :: String -> Infer (IORef a)
newInfer there = liftIO $ newIORef $ error $ "Panic! " ++ there
  ++ ": no result written?"

readInfer :: IORef t -> Infer t
readInfer = liftIO . readIORef

writeInfer :: IORef t -> t -> Infer ()
writeInfer ref t = liftIO $ writeIORef ref t

------------------------
-- Utilities
------------------------

lookupVar :: String -> Infer SigmaType
lookupVar n = do
  mst <- asks (flip lookupEnv n . env)
  case mst of
    Just sigma -> return sigma
    Nothing -> throwError $ "variable not in scope: " ++ n

extendEnv :: String -> SigmaType -> Infer a -> Infer a
extendEnv n s = local (\e -> e{env = (n,s):env e})

locallySubstEnv :: Substitution -> Infer a -> Infer a
locallySubstEnv s = local (\e -> e{env = substGamma s (env e)})

getEnvTypes :: Infer [SigmaType]
getEnvTypes = asks (map snd . env)

instantiate :: SigmaType -> Infer RhoType
instantiate (Forall tvs t) = do
  tvs' <- mapM (const newMetaTyVar) tvs
  return $ substTypeTV (zip tvs tvs') t
instantiate t = return t

-- compute deep skolemization of sigma by simultaneously
-- computing pr(sigma) and skolemizing it.
skolemize :: SigmaType -> Infer ([TyVar], RhoType)
skolemize (Forall tvs ty) = do -- rule PRPOLY
  sks1 <- mapM newSkolemTyVar tvs
  (sks2, ty') <- skolemize (substTypeTV (tvs `zip` map TyVar sks1) ty)
  return (sks1 ++ sks2, ty')
skolemize (Arrow aty rty) = do -- rule PRFUN
  (sks, rty') <- skolemize rty
  return (sks, Arrow aty rty')
skolemize t = return ([], t) -- rule PRMONO

quantify :: RhoType -> Infer SigmaType
quantify rho = do
  envTys <- getEnvTypes
  envTvs <- getMetaTyVars envTys
  rhoTvs <- getMetaTyVars [rho]
  let forallMvs = S.toList $ rhoTvs `S.difference` envTvs
  quantifyOnly forallMvs rho

closeOver :: RhoType -> Infer SigmaType
closeOver rho = quantifyOnly (S.toList $ freeMetaVars rho) rho

quantifyOnly :: [MetaTv] -> RhoType -> Infer SigmaType
quantifyOnly forallMvs rho = do
  let name (Meta n _) = BoundTv $ typeNames !! n
      forallTvs = map name forallMvs
  mapM_ bind (forallMvs `zip` forallTvs)
  Forall forallTvs <$> zonkType rho
  where
    bind (mv, name) = writeMv mv (TyVar name)

nextInt :: Infer Int
nextInt = do
  ctr <- asks supply
  lift . lift $ do
    -- use ++ctr instead of ctr++ because the value 0 is special
    -- so we want to start at 1.
    modifyIORef' ctr (+1)
    readIORef ctr

newMvRef :: Infer MvRef
newMvRef = liftIO $ newIORef Nothing

readMvRef :: MvRef -> Infer (Maybe TauType)
readMvRef r = liftIO $ readIORef r

writeMvRef :: MvRef -> Maybe TauType -> Infer ()
writeMvRef r t = liftIO $ writeIORef r t

readMv :: MetaTv -> Infer (Maybe TauType)
readMv (Meta _ ref) = readMvRef ref

writeMv :: MetaTv -> TauType -> Infer ()
writeMv (Meta _ ref) tau = writeMvRef ref (Just tau)

newMetaTyVar :: Infer TauType
newMetaTyVar = do
  fmap MetaTv $ Meta <$> nextInt <*> newMvRef

newSkolemTyVar :: TyVar -> Infer TyVar
newSkolemTyVar tv = do
  n <- nextInt
  return $ SkolemTv (UniqueName n (tvName tv))

-- | Giving a rho (which must be in weak-prenex form),
-- unify it with a function type.
unifyFun :: RhoType -> Infer (SigmaType, RhoType)
unifyFun = zonkType >=> go where
  go (Arrow aty rty) = return (aty, rty)
  go ft = do
    aty <- newMetaTyVar
    rty <- newMetaTyVar
    unify ft (Arrow aty rty)
    return (aty, rty)

getMetaTyVars :: [Type] -> Infer (S.Set MetaTv)
getMetaTyVars tys = S.unions . map freeMetaVars <$> mapM zonkType tys

getFreeTyVars :: [Type] -> Infer (S.Set TyVar)
getFreeTyVars tys = S.unions . map freeTyVars <$> mapM zonkType tys

--------------------------------------------
-- inference
--------------------------------------------

--- invariants
--- tcRho, instSigma: if Expected t is (Check t),
---   then t is in weak-prenex form.
--- checkRho, subsCheckRho: second argument is in weak-prenex form.

infer :: String -> (Expected a -> Infer ()) -> Infer a
infer label check = do
  expTy <- newInfer label
  check $ Infer expTy
  readInfer expTy

instSigma :: SigmaType -> Expected RhoType -> Infer ()
instSigma s (Infer r)   = instantiate s >>= writeInfer r
instSigma t1 (Check t2) = subsCheckRho t1 t2

checkSigma :: Exp -> SigmaType -> Infer ()
checkSigma e sigma = do
  (skolTvs, rho) <- skolemize sigma
  checkRho e rho
  envTys <- getEnvTypes
  escTvs <- getFreeTyVars (sigma : envTys)
  let badTvs = filter (`S.member` escTvs) skolTvs
      (s, their) = if length badTvs == 1 
        then (" ", "its") else ("s ", "their")
  unless (null badTvs) $ throwError $
    "Type of expression is not sufficiently polymorphic:\n" ++
    "  The (skolem) variable" ++ s ++ intercalate "," (map tvName badTvs) ++ "\n" ++
    "  would escape " ++ their ++ " scope"

inferSigma :: Exp -> Infer SigmaType
inferSigma e = do
  resTy <- inferRho e
  quantify resTy

checkRho :: Exp -> RhoType -> Infer ()
checkRho expr ty = tcRho expr (Check ty)

inferRho :: Exp -> Infer RhoType
inferRho exp = infer "inferRho" (tcRho exp)

tcRho :: Exp -> Expected RhoType -> Infer ()
tcRho (ConstExp c) expTy = instSigma (signature c) expTy

-- The initial Gamma will contain all of the constructor "functions"
-- and so constructor application is handled as a normal application
-- of a "variable" that happens to be bound to a constructor.
-- Basically: we don't have to do anything special here.
tcRho (VarExp x) expTy = do
  vSigma <- lookupVar x
  instSigma vSigma expTy

----------------------------------------------
-- if expressions
-- checking is easy; inference must enforce
-- that the two arms have isomorphic types w.r.t |-dsk*,
-- not w.r.t unify.
----------------------------------------------

tcRho (IfExp c t f) (Check ty) = do
  checkRho c boolType
  checkRho t ty
  checkRho f ty

tcRho (IfExp c t f) (Infer ref) = do
  checkRho c boolType
  rho1 <- inferRho t
  rho2 <- inferRho f
  -- enforce rho1 and rho2 are isomorphic w.r.t. |-dsk*
  subsCheck rho1 rho2
  subsCheck rho2 rho1
  -- report result type as rho1 (arbitrarily)
  writeInfer ref rho1

-- lists may only contain monotypes
tcRho (ListExp es) expTy = do
  eltTy <- newMetaTyVar
  instSigma (listType eltTy) expTy
  mapM_ (`checkRho` eltTy) es

-- This one is a little bit suspicious, in that we'd like to enforce
-- that all elements of the tuple type are monotypes and this definition
-- does not accomplish that goal. Rather, it enforces that
-- they are all rho types.
tcRho (TupleExp es) expTy = do
  rhos <- mapM inferRho es
  instSigma (tupleType rhos) expTy

tcRho (AppExp fun arg) expTy = do
  fty <- inferRho fun
  (aty, rty) <- unifyFun fty
  checkSigma arg aty
  instSigma rty expTy

--------------------------------------------------
-- fun exp: check/inference, annotated/not
--------------------------------------------------

-- ABS1: infer unannotated
tcRho (FunExp var Nothing body) (Infer ref) = do
  tau <- newMetaTyVar
  rho <- extendEnv var tau $ inferRho body
  writeInfer ref $ Arrow tau rho

-- ABS2: check unannotated
tcRho (FunExp var Nothing body) (Check expTy) = do
  (argTy, resTy) <- unifyFun expTy
  -- resTy is guaranteed to be a rho-type since expTy is
  -- in weak-prenex form by assumption.
  extendEnv var argTy $ checkRho body resTy

-- AABS1: infer annotated
tcRho (FunExp var (Just annTy) body) (Infer ref) = do
  rho <- extendEnv var annTy $ inferRho body
  writeInfer ref $ Arrow annTy rho

-- AABS2: check annotated
tcRho (FunExp var (Just annTy) body) (Check expTy) = do
  (sa, rho) <- unifyFun expTy
  subsCheck sa annTy
  extendEnv var annTy $ checkRho body rho

----------
-- done with fun exps
----------

tcRho (LetInExp x rhs body) expTy = do
  xSigma <- inferSigma rhs
  extendEnv x xSigma (tcRho body expTy)

tcRho (LetRecInExp f x rhs body) expTy = do
  tau1 <- newMetaTyVar
  tau2 <- newMetaTyVar
  let tauf = tau1 `funType` tau2
  tau3 <- extendEnv x tau1 $ extendEnv f tauf $ inferRho rhs
  unify tau2 tau3
  tauf' <- quantify tauf
  extendEnv f tauf' (tcRho body expTy)

tcRho (MonopExp op e) expTy = do
  opTy <- instantiate $ monopSignature op
  (argTy, resTy) <- unifyFun opTy
  checkRho e argTy
  instSigma resTy expTy

tcRho (BinopExp e1 op e2) expTy = do
  opTy <- instantiate $ binopSignature op
  (aty1,fty) <- unifyFun opTy
  (aty2,rty) <- unifyFun fty
  checkRho e1 aty1
  checkRho e2 aty2
  instSigma rty expTy

tcRho (AnnExp body annTy) expTy = do
  checkSigma body annTy
  instSigma annTy expTy

-- |-sh s1 <= s2
-- Invariant: the second argument is in weak-prenex form
subsCheck :: SigmaType -> SigmaType -> Infer ()
subsCheck sigma1 sigma2 = do -- rule DEEP-SKOL
  (skolTvs, rho2) <- skolemize sigma2
  subsCheckRho sigma1 rho2
  escTvs <- getFreeTyVars [sigma1, sigma2]
  let badTvs = filter (`S.member` escTvs) skolTvs
  unless (null badTvs) $ throwError $
       "Type is not polymorphic enough:\n"
    ++ "    actual: " ++ prettyType sigma1 ++ "\n"
    ++ "  expected: " ++ prettyType sigma2

-- |-dsk* s <= r
-- Invariant: the second argument is in weak-prenex form
subsCheckRho :: SigmaType -> RhoType -> Infer ()
subsCheckRho sigma1@(Forall _ _) rho2 = do -- rule SPEC
  rho1 <- instantiate sigma1
  subsCheckRho rho1 rho2
subsCheckRho t1 (Arrow a2 r2) = do -- rule FUN1
  (a1,r1) <- unifyFun t1
  subsCheckFun a1 r1 a2 r2
subsCheckRho (Arrow a1 r1) t2 = do -- rule FUN2
  (a2,r2) <- unifyFun t2
  subsCheckFun a1 r1 a2 r2
subsCheckRho tau1 tau2 = unify tau1 tau2 -- rule MONO

subsCheckFun :: SigmaType -> RhoType
             -> SigmaType -> RhoType
             -> Infer ()
subsCheckFun a1 r1 a2 r2 = do
  subsCheck    a2 a1 -- contra
  subsCheckRho r1 r2 -- co

{-
infer :: Exp -> Gamma -> Infer s Monotype
-- cases must be nonempty, because we can't parse an empty list of cases.
infer (MatchExp e (case1:cases)) gamma = do
  tau            <- infer e gamma
  (patTy, armTy) <- inferCase case1 gamma
  unify tau patTy
  forM_ cases $ \cas -> do
    (patTy, expTy) <- inferCase cas gamma
    unify tau patTy
    unify armTy expTy
  return armTy

inferCase :: MatchCase -> Gamma -> Infer s (Monotype, Monotype)
inferCase (MC{ casePat, caseExp }) gamma = do
  (patTy, ctx) <- inferPat casePat gamma
  let gamma' = unionEnv ctx gamma
  expTy <- infer caseExp gamma'
  return (patTy, expTy)

-- A helper function to infer the type of a pattern and also collect
-- all of the variables (and their types) introduced by the pattern.
-- Needs access to gamma so that it can disambiguate constructor names.
-- The returned environment contains ONLY the pattern variables and
-- their (inferred) types, not the rest of the input environment.
inferPat :: Pattern -> Gamma -> Infer s (Monotype, Gamma)
-- special case: tuple patterns
inferPat (Pat "*" args) _ = do
  tyVars <- mapM (const fresh) args
  let ty = tupleType tyVars
  patCtx <- lineUpPatArgs "" ty args
  return (ty, patCtx)

inferPat (Pat conName args) gamma = do
  conPolyType <- case lookupEnv gamma conName of
    -- how might we produce an error message that knows the
    -- actual type name? It's not easy (it's not always possible).
    Nothing -> throwError $ "constructor name not in scope: " ++ conName
    Just pt -> return pt
  conType <- instantiate conPolyType
  -- several cases depending on args and conType:
  -- if conType is a function type, args better not be empty
  --  1) args:[a], a : argType conType
  --  2) args:[a,b,...], conType must be a function from a tuple and arities must match
  -- else constructor is nullary, args better be empty.
  processPatWithTy conName conType args

-- given the type of a constructor and the arguments it was given
-- at the pattern site, compute the pattern type and pattern context.
processPatWithTy :: String -> Monotype -> [PatternVar] -> Infer s (Monotype, Gamma)
processPatWithTy cn (TyCon (UniqueName 0 "->") _) [] =
  throwError $ "constructor `" ++ cn ++ "' expects an argument"
processPatWithTy cn (TyCon (UniqueName 0 "->") [aty, rty]) args = do
  patCtx <- lineUpPatArgs cn aty args
  return (rty, patCtx)
processPatWithTy cn _ (_:_) = -- not a function type, but given patvars
  throwError $ "constructor `" ++ cn ++ "' is nullary, but has been give an argument"
processPatWithTy _ ty [] = return (ty, [])

-- given the type of a constructor's argument (often a tuple type), and a list
-- of the pattern vars that were the actual (possibly nested under a tuple)
-- arguments, line up the pattern vars against the tuple field types to make
-- a context. Drop wildcards and implode if the arities don't match.
lineUpPatArgs :: String -> Monotype -> [PatternVar] -> Infer s Gamma
lineUpPatArgs cn mt vars = cleanWildcards (Forall []) <$> go mt vars where
  go mt [v] = return [(v, mt)]
  go (TyCon (UniqueName 0 "*") tys) args
    | n <- length tys, m <- length args, n /= m = throwError $
        "constructor `" ++ cn ++ "' arg should have " ++ show n
        ++ " fields, but was given " ++ show m
    | otherwise = return $ zip args tys
  -- in this case, one argument (of non-tuple type) was expected,
  -- but a tuple was given. The missing argument case is handled in
  -- process... so we can ignore it here.
  go mt args = throwError $ "constructor `" ++ cn
    ++ "' has one field, but this pattern has " ++ show (length args)
-}

inferTop :: Exp -> Gamma -> Either String SigmaType
inferTop e = runInfer (inferSigma e)

------------------------------
-- Unifying
------------------------------

unify :: TauType -> TauType -> Infer ()
unify ty1 ty2
  | badType ty1 || badType ty2 = error 
    $ "Panic! Bad types in unify: " ++ prettyType ty1 ++ ", " ++ prettyType ty2
-- both skolems: fine if same skolem
unify (TyVar tv1)  (TyVar tv2)  | tv1 == tv2 = return ()
-- make sure not to point a metatv at itself!
unify (MetaTv tv1) (MetaTv tv2) | tv1 == tv2 = return ()
unify (MetaTv tv) ty = unifyVar tv ty
unify ty (MetaTv tv) = unifyVar tv ty
-- decompose arrows
unify (Arrow a1 r1) (Arrow a2 r2) = unify a1 a2 >> unify r1 r2
-- decompose general constructors
unify (TyCon c1 ts1) (TyCon c2 ts2)
  | c1 == c2 && length ts1 == length ts2
  = mapM_ (uncurry unify) $ zip ts1 ts2
-- fail
unify t1 t2 = typeMismatch t1 t2

unifyVar :: MetaTv -> TauType -> Infer ()
unifyVar tv1 ty2 = readMv tv1 >>= \case -- check if tv1 is already bound
  Just ty1 -> unify ty1 ty2
  Nothing  -> unifyUnboundVar tv1 ty2

-- | Given an UNBOUND MetaTv, unify it with the given TauType.
unifyUnboundVar :: MetaTv -> TauType -> Infer ()
unifyUnboundVar tv1 ty2@(MetaTv tv2) = readMv tv2 >>= \case
  -- tv1 /= tv2, since we didn't hit top case for MetaTv in unify
  Nothing -> writeMv tv1 ty2
  Just ty2' -> unify (MetaTv tv1) ty2'
unifyUnboundVar tv1 ty2 = occursCheck tv1 ty2 >> writeMv tv1 ty2

typeMismatch :: Type -> Type -> Infer a
typeMismatch ta tb = throwError $
    -- tb on the left because the usual path to unify via
    -- instSigma --> substCheckRho --> unify will end up
    -- with a (Check t) argument going down the right. That's
    -- the expected type, not the actual one.
      "Couldn't match expected type: " ++ prettyType tb ++
    "\n            with actual type: " ++ prettyType ta
  where
    tvScope = S.toList $ freeMetaVars ta `S.union` freeMetaVars tb
    prettyType ta@(TyCon (UniqueName n _) _ ) =
      prettyTypeWith tvScope ta ++ uniq n
    prettyType ta@(TyVar (SkolemTv (UniqueName n _))) =
      prettyTypeWith tvScope ta ++ uniq n
    prettyType ta = prettyTypeWith tvScope ta
    uniq = if needUniqs then \n -> "/" ++ show n else const ""
    uniqOf (TyCon un _) = Just un
    uniqOf (TyVar (SkolemTv un)) = Just un
    uniqOf _ = Nothing
    needUniqs = case (uniqOf ta, uniqOf tb) of
      (Just (UniqueName _ n1), Just (UniqueName _ n2)) -> n1 == n2
      _ -> False

occursCheck :: MetaTv -> TauType -> Infer ()
occursCheck ty mt = do
  fmvs <- getMetaTyVars [mt]
  let scope = S.toList fmvs
      lhs = prettyTypeWith scope (MetaTv ty)
      rhs = prettyTypeWith scope mt
  when (ty `S.member` fmvs) $
    throwError $
      "Cannot construct infinite type:\n"
      ++ "  " ++ lhs ++ " ~ " ++ rhs

-- | Eliminate any substitutions in the given type
zonkType :: Type -> Infer Type
zonkType (Forall ns ty) = Forall ns <$> zonkType ty
zonkType (Arrow arg res) = Arrow <$> zonkType arg <*> zonkType res
zonkType (TyCon c ts) = TyCon c <$> mapM zonkType ts
zonkType (TyVar n) = return (TyVar n)
zonkType (MetaTv mv) = readMv mv >>= \case
  Nothing -> return $ MetaTv mv
  Just ty -> do
    ty' <- zonkType ty
    writeMv mv ty'
    return ty'

-- | Should we panic if we see this type in a unification?
badType :: TauType -> Bool
badType (TyVar BoundTv{}) = True
badType _                 = False

------------------------------
-- Substitutions
------------------------------
type Substitution = [(MetaTv, TauType)]

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = mapSnd (substType s1) s2 ++ s1
  where mapSnd f = map (\(a, b) -> (a, f b))

delete :: MetaTv -> Substitution -> Substitution
delete n [] = []
delete n ((v,m):s)
  | n == v    = s
  | otherwise = (v,m) : delete n s

substTyVar :: Substitution -> MetaTv -> TauType
substTyVar s n = case lookup n s of
  Nothing -> MetaTv n
  Just mt -> mt

-- In a real program, we'd use a Substitutable typeclass here,
-- but I'm trying to keep this simple because we don't have
-- enough time this week to do all the type stuff and talk about
-- writing our own typeclasses.
substType :: Substitution -> Type -> Type
substType s (MetaTv n) = substTyVar s n
substType s (TyCon name tys) = TyCon name $ map (substType s) tys
substType s (TyVar tv) = TyVar tv
substType s (Arrow t1 t2) = Arrow (substType s t1) (substType s t2)
substType s (Forall tvs t) = Forall tvs t

-- substType, but getting rid of TyVars instead of MetaTvs.
-- This is useful for instantiate, and about nothing else.
substTypeTV :: [(TyVar, TauType)] -> Type -> Type
substTypeTV env (Arrow arg res) =
  Arrow (substTypeTV env arg) (substTypeTV env res)
substTypeTV env (TyVar n)       = fromMaybe (TyVar n) (lookup n env)
substTypeTV env (MetaTv mt)     = MetaTv mt
substTypeTV env (TyCon c ts)    = TyCon c (map (substTypeTV env) ts)
substTypeTV env (Forall ns rho) = Forall ns (substTypeTV env' rho)
  where env' = [(n,ty') | (n,ty') <- env, n `notElem` ns]

substGamma :: Substitution -> Gamma -> Gamma
substGamma s = map (\(n, ty) -> (n, substType s ty))

------------------------------
-- free variables
------------------------------

freeTyVars :: Type -> S.Set TyVar
freeTyVars (TyCon _ tys) = S.unions $ map freeTyVars tys
freeTyVars (TyVar n) = S.singleton n
freeTyVars (Arrow t1 t2) = freeTyVars t1 `S.union` freeTyVars t2
freeTyVars (MetaTv{}) = S.empty
freeTyVars (Forall tvs t) = freeTyVars t `S.difference` S.fromList tvs

freeMetaVars :: Type -> S.Set MetaTv
freeMetaVars (MetaTv mv) = S.singleton mv
freeMetaVars (TyCon _ tys) = S.unions $ map freeMetaVars tys
freeMetaVars (TyVar{}) = S.empty
freeMetaVars (Arrow t1 t2) = freeMetaVars t1 `S.union` freeMetaVars t2
freeMetaVars (Forall _ t) = freeMetaVars t

gammaMetavars :: Gamma -> S.Set MetaTv
gammaMetavars env = S.unions $ map (freeMetaVars . snd) env

------------------------------
-- utilities
------------------------------

signature :: Const -> SigmaType
signature IntConst{}    = Forall [] intType
signature FloatConst{}  = Forall [] floatType
signature BoolConst{}   = Forall [] boolType
signature StringConst{} = Forall [] stringType
signature UnitConst{}   = Forall [] unitType
signature NilConst{}    = Forall [BoundTv "a"] 
                        $ listType $ TyVar $ BoundTv "a"

monopSignature :: Monop -> SigmaType
monopSignature IntNegOp = Forall [] $ intType `funType` intType
monopSignature NotOp    = Forall [] $ boolType `funType` boolType

binopSignature :: Binop -> SigmaType
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
    binopType args res =
      Forall [] $ args `funType` (args `funType` res)
    cmpBinopType = 
      Forall [bv] $ var `funType` (var `funType` boolType)
    consType =
      Forall [bv] $ var `funType` (listType var `funType` listType var)
    bv = BoundTv "a"
    var = TyVar bv

intType    = TyCon (builtinName "int") []
floatType  = TyCon (builtinName "float") []
boolType   = TyCon (builtinName "bool") []
stringType = TyCon (builtinName "string") []
unitType   = TyCon (builtinName "unit") []

listType tau = TyCon (builtinName "list") [tau]
funType  = Arrow
tupleType = TyCon $ builtinName "*"

consName = UniqueName 0 "::"
nilName  = UniqueName 0 "[]"
consConstr = UserVal consName . Just -- has type consType
nilConstr  = UserVal nilName Nothing -- has type signature NilConst

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
  NilConst      -> nilConstr

evaluate (VarExp name) env = case lookupEnv env name of
  Nothing -> error "evaluate VarExp: not in env (impossible!)"
  Just v  -> v

evaluate (ListExp exps) env =
  let vs = map (flip evaluate env) exps
   in foldr (\hd tl -> consConstr (TupleVal [hd, tl])) nilConstr vs

evaluate (TupleExp exps) env =
  let vs = map (flip evaluate env) exps
   in TupleVal vs

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

evaluate (FunExp x _ e) env = CloVal x e env
evaluate (AppExp f e) env =
  let fv = evaluate f env
      v1 = evaluate e env
   in case fv of
      CloVal x b envf -> evaluate b $ insertEnv x v1 envf
      UserVal n Nothing -> UserVal n (Just v1)

evaluate (LetInExp x b e) env =
  let v1 = evaluate b env
   in evaluate e $ insertEnv x v1 env

evaluate (LetRecInExp f x b e) env =
  let clo = CloVal x b $ insertEnv f clo env
   in evaluate e $ insertEnv f clo env

evaluate (MatchExp e cases) env =
  let v = evaluate e env
      (patCtx, arm) = patternMatch v cases
   in evaluate arm (unionEnv patCtx env)

evaluate (AnnExp e _) env = evaluate e env

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

liftBinop ConsOp v1 v2 = consConstr (TupleVal [v1, v2])
liftBinop StrCatOp (StringVal s1) (StringVal s2) = StringVal $ s1 ++ s2

-- given a value and a list of match cases, pick a case,
-- returning the pattern context and case arm.
-- 'evaluate' doesn't have any way to raise errors because
-- typechecking prevents almost all possible evaluation errors.
-- However, "incomplete patterns" can't be avoided by _simply_ typechecking,
-- we would also need a coverage check, which isn't implemented
-- in this version. So if the user writes an incomplete pattern, the
-- interpreter will crash.
patternMatch :: Val -> [MatchCase] -> (Sigma, Exp)
-- the only 3 types of values we can match on are
-- UnitVal, TupleVal, and UserVal. All others are excluded by the type checker.
-- Note that we represent lists as UserVals.
patternMatch UnitVal (MC{caseExp} : _) = ([], caseExp) -- first case always matches
patternMatch (TupleVal vs) (MC{casePat = Pat "*" vars, caseExp} : _)
  = (cleanWildcards id $ zip vars vs, caseExp)
patternMatch (UserVal (UniqueName _ vn) v) cases = go cases where
  go [] = error "incomplete patterns!"
  go (case1:cases) = case testPattern (casePat case1) vn v of
    Just sigma -> (sigma, caseExp case1)
    Nothing    -> go cases

testPattern :: Pattern -> String -> Maybe Val -> Maybe Sigma
testPattern (Pat cn []) vn Nothing = matchWhen (cn == vn) []
testPattern (Pat cn [t]) vn (Just v) = matchWhen (cn == vn) [(t,v)]
testPattern (Pat cn as) vn (Just (TupleVal vs)) = matchWhen (cn == vn) $ zip as vs
-- otherwise, we're matching a pattern with arguments against a value without,
-- or vice versa. In this case, the constructor names definitely don't match,
-- we won't bother inspecting them.
testPattern (Pat _ []) _ Just{} = Nothing
testPattern (Pat _ (_:_)) _ Nothing = Nothing

-- helper function for testPattern. If condition is true, return
-- the given Sigma, otherwise fail the pattern.
matchWhen :: Bool -> [(PatternVar, Val)] -> Maybe Sigma
matchWhen b s = if b then Just $ cleanWildcards id s else Nothing

--------------------------------------------------------------------------------------
--
-- Statement Execution
--
--------------------------------------------------------------------------------------

type Result = (SigmaType, Val)
type Uniques = M.Map String Int
type Coherence = (Uniques {- type names -}, Uniques {- con names -})
type TopEnvs = (Sigma, Gamma, Coherence)

exec :: Statement -> TopEnvs -> Either String (Result, TopEnvs)
exec (AnonStmt e) envs@(sigma, gamma, (tus,_)) = do
  e <- renameTypesInExp tus e
  let mtau = inferTop e gamma
      v    = evaluate e sigma
  case mtau of
    Left err -> Left err
    Right tau -> Right ((tau, v), envs)
exec (LetStmt x _ e) (sigma, gamma, c@(tus,_)) = do
  e <- renameTypesInExp tus e
  let mtau = inferTop e gamma
      v    = evaluate e sigma
  case mtau of
    Left err -> Left err
    Right tau -> let sigma' = insertEnv x v sigma
                     gamma' = insertEnv x tau gamma
                     envs' = (sigma', gamma', c)
                 in Right ((tau, v), envs')
exec (LetRecStmt f x _ e) (sigma, gamma, c) = do
  term <- renameTypesInExp (fst c) (LetRecInExp f x e (VarExp f))
  let mtau = inferTop term gamma
  case mtau of
    Left err -> Left err
    Right tau ->
      let clo = CloVal x e sigma'
          sigma' = insertEnv f clo sigma
          gamma' = insertEnv f tau gamma
          envs' = (sigma', gamma', c)
      in Right ((tau, clo), envs')

exec (TypeStmt (Sig tyargs tyname cdecls)) (s, g, (t, c)) = do
    _ <- noDuplicateTyVars tyargs
    _ <- noDuplicateConNames cdecls
    (cdecls', uniques) <- mapAndUnzipM (uniqifyConDecl (t', c)) cdecls
    let bindings = map (makeConDeclBindings tyvars newTyName) cdecls'
        (s', g') = foldr insertCDecl (s, g) bindings
        typeBindings = map (\(n,_,t) -> (n,t)) bindings
        updates = map parts uniques
        c' = M.fromList updates `M.union` c
    _ <- mapM_ (uncurry notExistential) typeBindings
    return ((Forall [] unitType, UnitVal), (s', g', (t', c')))
  where
    tyvars = map BoundTv tyargs
    parts (UniqueName n s) = (s, n)
    insertCDecl (name, v, t) (sigma, gamma)
      = (insertEnv name v sigma, insertEnv name t gamma)

    -- default is not really needed, because the tyname is in t' by construction
    newTyName = UniqueName (M.findWithDefault 1 tyname t') tyname
    t' = M.insertWith (+) tyname 1 t

notExistential :: String -> SigmaType -> Either String ()
notExistential conName pt
  | null $ freeMetaVars pt = return ()
  | otherwise = throwError $ unwords
    ["constructor", conName, "is existential"]

noDuplicateTyVars :: [String] -> Either String ()
noDuplicateTyVars tyargs
  | length tyargs == length (S.toList (S.fromList tyargs)) = return ()
  | otherwise = throwError "duplicate type variable names"

noDuplicateConNames :: [ConDecl] -> Either String ()
noDuplicateConNames cdecls
  | length names == length (S.toList (S.fromList names)) = return ()
  | otherwise = throwError "duplicate constructor names"
  where nameOfCDecl (ConDecl (UniqueName 0 n) _) = n
        nameOfCDecl _ = error "Parsed conName with n /= 0?"
        names = map nameOfCDecl cdecls

uniqifyConDecl :: Coherence -> ConDecl -> Either String (ConDecl, UniqueName)
uniqifyConDecl c@(tyUs, conUs) (ConDecl (UniqueName _ name) mtau) =
  case mtau of
    Nothing  -> pure (ConDecl u Nothing, u)
    Just tau -> uniqify tau <&> \ut -> (ConDecl u (Just ut), u)
  where
    conUs' = M.insertWith (+) name 1 conUs
    u = UniqueName (M.findWithDefault 1 name conUs') name
    uniqify = renameType tyUs

makeConDeclBindings :: [TyVar] -> UniqueName -> ConDecl -> (String, Val, SigmaType)
makeConDeclBindings tyvars tyname (ConDecl un@(UniqueName _ name) Nothing)
  = (name, UserVal un Nothing, Forall tyvars $ TyCon tyname $ map TyVar tyvars)
makeConDeclBindings tyvars tyname (ConDecl un@(UniqueName _ name) (Just mt))
  = (name, UserVal un Nothing, Forall tyvars conType)
  where
    conType = mt `funType` TyCon tyname (map TyVar tyvars)

--------------------------------------------------------------------------------------
--
-- Prettier Printing
--
--------------------------------------------------------------------------------------

prettyTypeWith :: [MetaTv] -> Type -> String
prettyTypeWith vars = pretty
  where
    pretty ty = case ty of
      TyVar (BoundTv n) -> n
      TyVar (SkolemTv (UniqueName _ n)) -> n
      MetaTv mv -> nameOf mv
      -- correctly handling this case really needs some kind of precedence
      -- knowledge, so instead for now we'll just aggressively always use
      -- parentheses.
      Arrow t1 t2 -> parens $ unwords [pretty t1, "->", pretty t2]
      TyCon (UniqueName 0 "*") ts       -> parens $ intercalate " * " (map pretty ts)

      TyCon (UniqueName _ name) []  -> name
      TyCon (UniqueName _ name) [t] -> unwords [pretty t, name]
      TyCon (UniqueName _ name) ts  ->
        parens (intercalate ", " (map pretty ts)) ++ " " ++ name

      Forall [] t -> pretty t
      Forall ts t -> parens $ "∀" ++ intercalate "," (map unTv ts)
                           ++ ". " ++ pretty t
        where
          unTv (BoundTv n) = n
          unTv (SkolemTv (UniqueName _ n)) = n

    nameOf = assocNames vars
    parens s = "(" ++ s ++ ")"

prettyType :: Type -> String
prettyType t = prettyTypeWith (S.toList $ freeMetaVars t) t

typeNames :: [String]
typeNames = bad : map ('\'':) ([1..] >>= flip replicateM ['a'..'z'])
  where bad = error "skolem variable with unique 0?"

assocNames :: [MetaTv] -> (MetaTv -> String)
assocNames vars = nameOf
  where
    nameAssocs = zip vars (tail typeNames)
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
  TupleVal vs   -> "(" ++ intercalate ", " (map prettyVal vs) ++ ")"
  UserVal (UniqueName 0 "[]") Nothing -> "[]"
  UserVal (UniqueName 0 "::") (Just v) -> "[" ++ intercalate "; " (map prettyVal $ unpack v) ++ "]"
  UserVal (UniqueName _ n) (Just v) -> unwords [n, prettyVal v]
  UserVal (UniqueName _ n) Nothing  -> n
  CloVal{}      -> "<<closure>>"
  where
    -- unpack chain of consConstrs into a (haskell) list
    unpack (TupleVal [hd, tl]) = hd : unpackUser tl
    -- other cases will raise an error, but they are ill-typed and can't happen!
    unpackUser (UserVal (UniqueName 0 "[]") Nothing) = []
    unpackUser (UserVal (UniqueName 0 "::") (Just v)) = unpack v

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

replPretty :: Either String Result -> String
replPretty (Left err) = err
replPretty (Right (ty, v)) = prettyVal v ++ " : " ++ prettyType ty

replPrint :: Either String Result -> IO ()
replPrint = putStrLn . replPretty

repl :: TopEnvs -> IO ()
repl envs = do
  mstmt <- replRead
  case mstmt of
    Nothing -> return () -- done
    Just stmt -> case exec stmt envs of
      Left err -> replPrint (Left err) >> repl envs
      Right (r, envs') -> replPrint (Right r) >> repl envs'

initialTyUs = M.fromList $ map (\s -> (s,0))
  ["list", "*", "->",
   "int", "float",
   "bool", "unit",
   "string" ]

initialSigma :: Sigma
initialSigma = [] -- no need for bindings for "[]" and "::";
                  -- they aren't really identifiers, and outside of patterns
                  -- they are special syntax.

initialGamma :: Gamma
initialGamma = -- In contrast, they are not special in patterns, so they
               -- must be given types for inferPat to lookup.
  [ ("[]", signature NilConst)
  , ("::", Forall [BoundTv "a"] $ tupleType [tv0, lst] `funType` lst)
  , ("()", signature UnitConst)
  ]
  where tv0 = TyVar btv; lst = listType tv0
        btv = BoundTv "a"

initialTopEnvs :: TopEnvs
initialTopEnvs = (initialSigma, initialGamma, (initialTyUs, M.empty))

main :: IO ()
main = repl (initialSigma, initialGamma, (initialTyUs, M.empty))


{-

type church = forall a. (a -> a) -> (a -> a)

add : church -> church -> church
===>  (forall a. (a -> a) -> (a -> a)) -> church -> church

-}


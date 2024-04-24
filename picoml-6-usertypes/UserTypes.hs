module UserTypes where

import Control.Applicative (liftA2)
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Writer

import Data.Functor (($>))
import Data.List (intercalate)
import Data.Set qualified as S
import Data.Map qualified as M

import Text.Parsec hiding (State, parse)
import Text.Parsec qualified as Parsec (parse)
import Text.Parsec.Language
import Text.Parsec.Expr
import Text.Parsec.Token qualified as T
import Text.Parsec.String

import Debug.Trace

--------------------------------------------------------------------------------------
--
-- Language Data Types
--
--------------------------------------------------------------------------------------

data Statement
  = AnonStmt Exp        -- e;;
  | LetStmt  String Exp -- let x = e;;
  | LetRecStmt String String Exp -- let rec f x = e;;
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
  | FunExp   String Exp
  | AppExp   Exp Exp
  | LetInExp String Exp Exp
  | LetRecInExp String String Exp Exp
    -- Pattern matching!
    -- Match a "scrutinee" against a bunch of possible
    -- patterns, picking the pattern that matches. For now,
    -- we don't support any nested pattern matching. So we
    -- only support basic non-nested patterns. However, since
    -- our constructors can only have on argument, which is
    -- usually a tuple, that would be unpalatable without help.
    -- So we support one basic case of nested patterns;
    -- Foo (x, y, ...) is allowed. As a result, the inferPattern
    -- and patternMatch functions are fairly ad-hoc.
  | MatchExp Exp [MatchCase]
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

data MonotypeF id
  = TyCon UniqueName [MonotypeF id]
  | TyVar id
  deriving (Eq, Show)
type Monotype = MonotypeF TyVar
type ParsedMonotype = MonotypeF String

data UniqueName = UniqueName Int String -- int will be 0 for builtin, >= 1 for user
                -- however, the parser always outputs 0, and it will be fixed in exec
                -- before adding anything to the environment
  deriving (Eq, Ord, Show)

data ConDecl = ConDecl UniqueName (Maybe ParsedMonotype)
  -- ConDecl Name Nothing                           ===>     | Name
  -- ConDecl Name (Just (TyVar ...))                ===>     | Name of 'a
  -- ConDecl Name (Just (TyCon tupleType [f1,...])) ===>     | Name of f1 * ...
  -- Syntactically these cases are different, but semantically the only separation
  -- is between the first case and the other two. Either the constructor is nullary,
  -- or it takes one argument, which might be a tuple.
  deriving (Eq, Show)

builtinName :: String -> UniqueName
builtinName = UniqueName 0

type TyVar = Int

data Polytype = Forall [TyVar] Monotype
  deriving (Eq, Show)

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
type Gamma = Env Polytype
type Sigma = Env Val
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
    , "::"
    , "&&", "||"
    , "^"
    ]
  , T.reservedNames =
    [ "true", "false"
    , "let", "rec", "in"
    , "if", "then", "else"
    , "type", "of"
    , "match", "with", "_"
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
           <|> parseMatch
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
  t <- optionMaybe $ reserved "of" *> parseMonotype
  -- create a builtin name for the constructor. In order to "execute" a
  -- TypeStmt, we'll need to assign a fresh number to the signature
  -- (that is, the name of the type and all of its constructors) of
  -- the TypeStmt. This number will disambiguate among types that
  -- shadow each other. But we can't do it yet, because we don't know
  -- in the parser how many other type names we've read. In a real compiler,
  -- we have the same problem: this disambiguation is a _semantic_ analysis,
  -- not a _syntactic_ analysis.
  return $ ConDecl (UniqueName 0 n) t

parseMonotype :: Parser ParsedMonotype
parseMonotype = parseProdType

parseProdType :: Parser ParsedMonotype
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
  where singleton x = [x]

parseAType :: Parser ParsedMonotype
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

parseTypeParams :: Parser [ParsedMonotype]
parseTypeParams =
    (singleton . TyVar <$> typeIdentifier)
    <|> (singleton . conOf <$> identifier)
    <|> parens (parseMonotype `sepBy1` reserved ",")
  where
    conOf name = TyCon (UniqueName 0 name) []
    singleton x = [x]

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

-- | Run an 'Infer' action, gathering the constraints that it emitted.
-- The constraints are also emitted by the result. This is necessary to
-- avoid losing constraint information about monotype variables which
-- are used only in the RHS of a let-binding.
gather :: Infer a -> Infer (a, [Constraint])
gather = {- censor (const []) .-} listen

infer :: Exp -> Gamma -> Infer Monotype

infer (ConstExp c) _ = instantiate $ signature c

-- The initial Gamma will contain all of the constructor "functions"
-- and so constructor application is handled as a normal application
-- of a "variable" that happens to be bound to a constructor.
-- Basically: we don't have to do anything special here.
infer (VarExp name) gamma = case lookupEnv gamma name of
  Just tau -> instantiate tau
  Nothing  -> throwError $ "variable name not in scope: " ++ name

infer (ListExp es) gamma = do
  taus <- mapM (flip infer gamma) es
  _    <- unifyMany taus
  case taus of
    [] -> listType <$> fresh
    (t:_) -> return $ listType t
  where
    unifyMany []  = pure ()
    unifyMany [t] = pure ()
    unifyMany (t1:t2:ts) = unify t1 t2 >> unifyMany (t2:ts)

infer (TupleExp es) gamma = do
  taus <- mapM (flip infer gamma) es
  return $ TyCon (builtinName "*") taus

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
  (taub, phi) <- gather $ infer b gamma
  subst       <- liftEither $ solve phi
  let sGamma = substGamma subst gamma
      sTaub  = substMonotype subst taub
      taub' = generalize sGamma sTaub
  infer e (insertEnv x taub' gamma)

infer (LetRecInExp f x b e) gamma = do
  tau1        <- fresh
  tau2        <- fresh
  let tauf = tau1 `funType` tau2
  (tau3, phi) <- gather $ infer b
                 $ insertEnv x (Forall [] tau1) $ insertEnv f (Forall [] tauf) gamma
  subst       <- liftEither $ solve $ (tau2, tau3) : phi
  let sGamma = substGamma subst gamma
      sTauf  = substMonotype subst tauf
  infer e $ insertEnv f (generalize sGamma sTauf) sGamma

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

inferCase :: MatchCase -> Gamma -> Infer (Monotype, Monotype)
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
inferPat :: Pattern -> Gamma -> Infer (Monotype, Gamma)
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
processPatWithTy :: String -> Monotype -> [PatternVar] -> Infer (Monotype, Gamma)
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
lineUpPatArgs :: String -> Monotype -> [PatternVar] -> Infer Gamma
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
  | equal = solve (zip as bs ++ rest)
  | otherwise = throwError $
    "Couldn't match expected type: " ++ prettyType ta ++
    "\n            with actual type: " ++ prettyType tb
  where
    tvScope = S.toList $ monotypeFvs ta `S.union` monotypeFvs tb
    prettyType ta@(TyCon (UniqueName n _) _ ) =
      prettyMonotypeWith tvScope ta ++ uniq n
    uniq = if needUniqs then \n -> "/" ++ show n else const ""
    needUniqs = case (a, b) of
      (UniqueName _ n1, UniqueName _ n2) -> n1 == n2

    equal = a == b && length as == length bs

occursCheck :: TyVar -> Monotype -> Bool
occursCheck ty mt = ty `S.member` monotypeFvs mt

------------------------------
-- Substitutions
------------------------------
type Substitution = [(TyVar, Monotype)]

compose :: Substitution -> Substitution -> Substitution
compose s1 s2 = mapSnd (substMonotype s1) s2 ++ s1
  where mapSnd f = map (\(a, b) -> (a, f b))

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
substGamma s = map (\(n, ty) -> (n, substPolytype s ty))

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

intType    = TyCon (builtinName "int") []
floatType  = TyCon (builtinName "float") []
boolType   = TyCon (builtinName "bool") []
stringType = TyCon (builtinName "string") []
unitType   = TyCon (builtinName "unit") []

listType tau = TyCon (builtinName "list") [tau]
funType  tau1 tau2 = TyCon (builtinName "->") [tau1, tau2]
tupleType = TyCon $ builtinName "*"

-- resultType "walks over" an arrow type like A -> B -> C
-- until it runs out of arrows, and then returns the eventual
-- result type of the function. In that examle, C.
resultType (TyCon (UniqueName 0 "->") [_, t2]) = resultType t2
resultType t = t

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

evaluate (FunExp x e) env = CloVal x e env
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


type Result = (Polytype, Val)
type Uniques = M.Map String Int
type Coherence = (Uniques {- type names -}, Uniques {- con names -})
type TopEnvs = (Sigma, Gamma, Coherence)

exec :: Statement -> TopEnvs -> Either String (Result, TopEnvs)
exec (AnonStmt e) envs@(sigma, gamma, _) =
  let mtau = inferTop e gamma
      v    = evaluate e sigma
  in case mtau of
      Left err -> Left err
      Right tau -> Right ((tau, v), envs)
exec (LetStmt x e) (sigma, gamma, c) =
  let mtau = inferTop e gamma
      v    = evaluate e sigma
  in case mtau of
      Left err -> Left err
      Right tau -> let sigma' = insertEnv x v sigma
                       gamma' = insertEnv x tau gamma
                       envs' = (sigma', gamma', c)
                   in Right ((tau, v), envs')
exec (LetRecStmt f x e) (sigma, gamma, c) =
  let mtau = inferTop (LetRecInExp f x e (VarExp f)) gamma
      v    = evaluate e sigma
  in case mtau of
      Left err -> Left err
      Right tau ->
        let clo = CloVal x e sigma'
            sigma' = insertEnv f clo sigma
            gamma' = insertEnv f tau gamma
            envs' = (sigma', gamma', c)
        in Right ((tau, clo), envs')

exec (TypeStmt (Sig tyargs tyname cdecls)) (s, g, (t, c)) = do
    _ <- mapM_ (uncurry notExistential) typeBindings
    _ <- noDuplicateTyVars tyargs
    _ <- noDuplicateConNames cdecls
    return ((Forall [] unitType, UnitVal), (s', g', (t', c')))
  where
    renaming = zip tyargs [0..]
    (s', g') = foldr insertCDecl (s, g) bindings
    (cdecls', uniques) = unzip $ map (uniqifyConDecl (t', c)) cdecls
    
    bindings = map (makeConDeclBindings renaming newTyName) cdecls'
    insertCDecl (name, v, t) (sigma, gamma)
      = (insertEnv name v sigma, insertEnv name t gamma)

    typeBindings = map (\(n,_,t) -> (n,t)) bindings

    -- default is not really needed, because the tyname is in t' by construction
    newTyName = UniqueName (M.findWithDefault 1 tyname t') tyname
    t' = M.insertWith (+) tyname 1 t
    c' = M.fromList updates `M.union` c
    updates = map parts uniques
      where parts (UniqueName n s) = (s, n)

notExistential :: String -> Polytype -> Either String ()
notExistential conName pt
  | null $ polytypeFvs pt = return ()
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
  where nameOfCDecl (ConDecl n _) = n
        names = map nameOfCDecl cdecls

uniqifyConDecl :: Coherence -> ConDecl -> (ConDecl, UniqueName)
uniqifyConDecl c@(tyUs, conUs) (ConDecl (UniqueName _ name) mtau) =
  case mtau of
    Nothing  -> (ConDecl u Nothing, u)
    Just tau -> (ConDecl u (Just $ uniqify tau), u)
  where
    conUs' = M.insertWith (+) name 1 conUs
    u = UniqueName (M.findWithDefault 1 name conUs') name
    
    uniqify (TyVar n) = TyVar n
    uniqify (TyCon (UniqueName _ name) taus) =
      TyCon (UniqueName (M.findWithDefault 1 name tyUs) name) $ map uniqify taus

makeConDeclBindings :: Env TyVar -> UniqueName -> ConDecl -> (String, Val, Polytype)
makeConDeclBindings naming tyname (ConDecl un@(UniqueName _ name) Nothing)
  = (name, UserVal un Nothing, Forall vars $ TyCon tyname $ map TyVar vars)
  where vars = map snd naming
makeConDeclBindings naming tyname (ConDecl un@(UniqueName _ name) (Just mt))
  = (name, UserVal un Nothing, Forall vars conType)
  where
    vars = map snd naming
    conType = rename mt `funType` TyCon tyname (map TyVar vars)

    rename (TyVar s) = TyVar $ case lookupEnv naming s of
      Just i -> i
      Nothing -> (-1)
    rename (TyCon n ts) = TyCon n $ map rename ts

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
      -- correctly handling this case really needs some kind of precedence
      -- knowledge, so instead for now we'll just aggressively always use
      -- parentheses.
      TyCon (UniqueName 0 "->") [t1,t2] -> parens $ unwords [pretty t1, "->", pretty t2]
      TyCon (UniqueName 0 "*") ts       -> parens $ intercalate " * " (map pretty ts)

      TyCon (UniqueName _ name) []  -> name
      TyCon (UniqueName _ name) [t] -> unwords [pretty t, name]
      TyCon (UniqueName _ name) ts  ->
        parens (intercalate ", " (map pretty ts)) ++ " " ++ name

    nameOf = assocNames vars
    parens s = "(" ++ s ++ ")"

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
  TupleVal vs   -> "(" ++ intercalate ", " (map prettyVal vs) ++ ")"
  UserVal (UniqueName 0 "[]") Nothing -> "[]"
  UserVal (UniqueName 0 "::") (Just v) -> "[" ++ intercalate "; " (map prettyVal $ unpack v) ++ "]"
  UserVal (UniqueName _ n) (Just v) -> unwords [n, prettyVal v]
  UserVal (UniqueName _ n) Nothing  -> n
  CloVal{}      -> "<<closure>>"
  where
    -- unpack  chain of consConstrs into a (haskell) list
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
replPretty (Right (ty, v)) = prettyVal v ++ " : " ++ prettyPolytype ty

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

initialTyUs = M.fromList $ map (\s -> (s,0)) ["list", "*", "->"]

initialSigma :: Sigma
initialSigma = [] -- no need for bindings for "[]" and "::";
                  -- they aren't really identifiers, and outside of patterns
                  -- they are special syntax.

initialGamma :: Gamma
initialGamma = -- In contrast, they are not special in patterns, so they
               -- must be given types for inferPat to lookup.
  [ ("[]", signature NilConst)
  , ("::", Forall [0] $ tupleType [tv0, lst] `funType` lst)
  , ("()", signature UnitConst)
  ]
  where tv0 = TyVar 0; lst = listType (TyVar 0)

main = repl (initialSigma, initialGamma, (initialTyUs, M.empty))

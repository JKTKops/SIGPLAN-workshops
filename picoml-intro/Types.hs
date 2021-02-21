module Types where

data Exp
  = VarExp String
  | ConstExp Const
  | MonOpAppExp MonOp Exp
  | BinOpAppExp Exp BinOp Exp
  | IfExp Exp Exp Exp
  | AppExp Exp Exp
  | FunExp String Exp
  | LetExp String Exp Exp
  | LetRecExp String String Exp Exp
  --  | RaiseExp Exp
  --  | TryWithExp Exp [(Int, Exp)] (Maybe Int, Exp)
  --                   [Exp] < to typecheck only

data Declaration
  = AnonDec Exp
  | LetDec  String Exp
  | LetRec  String String Exp

data Const
  = BoolConst Bool
  | IntConst Integer
  | FloatConst Double
  | StringConst String
  | NilConst | UnitConst

data MonOp
  = HdOp | TlOp | PrintOp | IntNegOp | FstOp | SndOp

data BinOp
  = IntPlusOp | IntMinusOp | IntTimesOp | IntDivOp -- + | - | * | /
  | FloatPlusOp | FloatMinusOp | FloatTimesOp | FloatDivOp -- +. | -. | *. | /.
  | ConcatOp
  | ConsOp
  | CommaOp
  | EqOp | GreaterOp
  | ModOp
  | ExpoOp

type Env a = [(String, a)]
type Memory = Env Value
data Value
  = UnitVal
  | BoolVal Bool
  | IntVal Integer
  | FloatVal Double
  | StringVal String
  | PairVal Value Value
  | ListVal [Value]
  | Closure String Exp Memory
  --  | Exn Int
{-

type memory = (string * value) list
 and value =
   ...
   | Closure of string * exp * memory
   | RecVarVal of string * string * exp * memory

-}

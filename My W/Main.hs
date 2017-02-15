import qualified Data.Map as M
import Data.Map(Map)

data Type
  = TInt
  | TBool
  | TArr Type Type

data Op
  = Add Expr Expr
  | Mult Expr Expr

data Expr
  = Var String
  | Lam [String] Expr
  | App Expr Expr
  | Op Op

data Constraints
  = ConsPair Expr Expr
  | ConstType Expr Type

congen (Var n) = []
congen (Lam ns body) = congen body
congen t@(App e1 e2) = [ConsPair e1 (ConstType t (TArr ...))] ++ congen e1 ++ congen e2
congen (Op (Add e1 e2)) = ConstType e1 TInt : ConstType e2 TInt : congen e1 ++ congen e2
congen (Op (Mult e1 e2)) = ConstType e1 TInt : ConstType e2 TInt : congen e1 ++ congen e2

main = print "Hello"

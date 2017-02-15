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
  = EqCons Expr Expr

type TEnv = Map Expr Type -- What the hell is this supposed to do? Why did I add it?

congen (Var n) = []
congen (Lam ns body) = congen body
congen (App e1 e2) = [EqCons e1 e2] ++ congen e1 ++ congen e2
congen (Op (Add e1 e2)) = [EqCons e1 e2] ++ congen e1 ++ congen e2
congen (Op (Mult e1 e2)) = [EqCons e1 e2] ++ congen e1 ++ congen e2

main = print "Hello"

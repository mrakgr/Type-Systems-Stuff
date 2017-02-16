import Control.Monad.State

import qualified Data.Map as M
import Data.Map(Map)

data Type
  = TInt
  | TBool
  | TArr Type Type
  | TGeneric Int

data Op
  = Add Expr Expr
  | Mult Expr Expr

data Expr
  = Var String
  | Lam [String] Expr
  | App Expr Expr
  | Op Op

data TEnv = Map Expr Type

typeof = do
  s <- get

infer (Var n) = []
infer (Lam ns body) = congen body
infer t@(App e1 e2) = [ConsPair e1 (ConstType t (TArr ...))] ++ congen e1 ++ congen e2
infer (Op (Add e1 e2)) = ConstType e1 TInt : ConstType e2 TInt : congen e1 ++ congen e2
infer (Op (Mult e1 e2)) = ConstType e1 TInt : ConstType e2 TInt : congen e1 ++ congen e2

main = print "Hello"

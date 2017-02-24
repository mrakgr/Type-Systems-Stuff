-- Simple bidirecdtional typechecker for simply typed lambda calculus.
-- From: https://jozefg.bitbucket.io/posts/2014-11-22-bidir.html

import Control.Monad

data Ty = Bool
        | Arr Ty Ty
        deriving(Eq, Show)

data IExpr = Var Int
           | App IExpr CExpr
           | Annot CExpr Ty
           | If CExpr IExpr IExpr
           | ETrue
           | EFalse

data CExpr = Lam CExpr
           | CI IExpr

type Env = [Ty]

(?!) :: [a] -> Int -> Maybe a
xs ?! i = if i < length xs then Just (xs !! i) else Nothing

inferType :: Env -> IExpr -> Maybe Ty
inferType env (Var i) = env ?! i
inferType env (App l r) =
  case inferType env l of
   Just (Arr lTy rTy) -> checkType env r lTy >> return rTy
   _ -> Nothing
inferType env (Annot e an) = checkType env e an >> return an
inferType _ ETrue = return Bool
inferType _ EFalse = return Bool
inferType env (If i t e) = do
  checkType env i Bool
  lTy <- inferType env t
  rTy <- inferType env e
  guard (lTy == rTy)
  return lTy

checkType :: Env -> CExpr -> Ty -> Maybe ()
checkType env (Lam ce) (Arr l r) = checkType (l : env) ce r
checkType env (CI e) t = inferType env e >>= guard . (t ==)
checkType _ _ _ = Nothing

main = return ()

{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

import Control.Monad.State.Strict
import Control.Monad.Except
import Data.Maybe

import qualified Data.IntMap as IM
import Data.IntMap(IntMap)

import qualified Data.Map as M
import Data.Map(Map)



type VarName = String
data Term
  = V VarName
  | L VarName Term
  | A Term Term
  | I Int
  | Term :+ Term
  | IFZ Term Term Term
  | Fix Term
  deriving (Show, Eq)
infixl 9 `A`

data Typ = TInt | Typ :> Typ | TV TVarName deriving (Show, Eq)
type TVarName = Int
infixr 9 :>

data TVE = TVE Int (IntMap Typ)

--newtv :: TVE -> (Typ, TVE)
newtv = do
  (TVE n s) <- get
  put $ TVE (n+1) s
  return $ TV n

tve0 :: TVE
tve0 = TVE 0 IM.empty

tvlkup :: TVE -> TVarName -> Maybe Typ
tvlkup (TVE _ s) v = IM.lookup v s

tvext :: TVE -> (TVarName, Typ) -> TVE
tvext (TVE c s) (tv,t) = TVE c (IM.insert tv t s)

tvsub :: TVE -> Typ -> Typ
tvsub tve (t1 :> t2) = tvsub tve t1 :> tvsub tve t2
tvsub tve (TV v) | Just t <- tvlkup tve v = tvsub tve t
tvsub tve t = t

unify = \t1 t2 -> do
  tve <- get
  unify' (tvchase tve t1) (tvchase tve t2) tve where

  -- chase through a substitution ‘shallowly’:
  -- stop at the last equivalent type variable
  tvchase :: TVE -> Typ -> Typ
  tvchase tve (TV v) | Just t <- tvlkup tve v = tvchase tve t
  tvchase _ t = t

  -- If either t1 or t2 are type variables, they must be unbound
  unify' TInt TInt = return ()
  unify' (t1a :> t1r) (t2a :> t2r) = do
    _ <- unify t1r t2r
    _ <- unify t1a t2a
    return ()
  unify' (TV v1) t2 = unifyv v1 t2
  unify' t1 (TV v2) = unifyv v2 t1
  unify' t1 t2 = throwError $ Left $ unwords ["constant mismatch:", show t1, show t2]

  unifyv v1 (TV v2) | v1 == v2 = return ()

  unifyv v1 t2 = do
    is_occurs <- occurs v1 t2

    if is_occurs then
      throwError $ Left $ unwords ["occurs check:", show (TV v1), "in", show (tvsub tve t2)]
    else do
      modify $ \tve -> tvext tve (v1,t2)
      return ()  -- record new constraint

    where
      -- I've rewriten this like so because the lookup might otherwise miss the case where
      -- v1 and TV v2 are equal if it is called from outside of unifyv.
      -- While Oleg's version works as intended, having the occurs function at the top level
      -- definitely implies things about its structure that are false.
      occurs v TInt = return False
      occurs v (t1 :> t2) = liftM2 (||) (occurs v t1) (occurs v t2)
      occurs v (TV v2) = do
        tve <- get
        case tvlkup tve v2 of
          Nothing -> return False -- This is always false because of the `unifyv v1 (TV v2) tve | v1 == v2 = Right tve` line
          Just t -> occurs v t tve

type TEnv = Map VarName Typ

lkup env x = fromMaybe err $ M.lookup x env
  where err = error $ "Unbound variable " ++ x
env0 = M.empty
ext = M.insert

--teval' :: TEnv -> Term -> TVE -> (Typ,TVE)
teval' tenv t =
  case t of
    V x -> return (lkup tenv x)
    L x e -> do
      tv <- newtv
      te <- teval' (ext x tv tenv) e
      return (tv :> te)
    A e1 e2 -> do
      t1 <- teval' tenv e1
      t2 <- teval' tenv e2
      t1r <- newtv
      unify t1 (t2 :> t1r) >>= \case
        Right tve -> return (t1r,tve)
        Left err -> error err
    I n ->
      return TInt
    e1 :+ e2 ->
      let (t1,tve) = teval' tenv e1 tve in
      let (t2,tve) = teval' tenv e2 tve in
      case either Left (unify t2 TInt) $  unify t1 TInt tve of
        Right tve -> (TInt,tve)
        Left err -> error $ "Trying to add non-integers: " ++ err
    Fix e ->
      let (t,tve) = teval' tenv e tve in
      let (ta,tve) = newtv tve in
      let (tb,tve) = newtv tve in
      -- It never occurred to me, but it maybe the `->` type arrows are right associative in ML?
      case unify t ((ta :> tb) :> ta :> tb) tve of
        Right tve -> (ta :> tb,tve)
        Left err -> error $ "Inappropriate type in Fix: " ++ err

teval :: TEnv -> Term -> Typ
teval tenv e =
  let (t,tve) = teval' tenv e tve0 in
  tvsub tve t

(vx,vy) = (V "x", V "y")
test0 = teval env0 ((L "x" (vx :+ (I 2))) `A` (I 1))
-- (TV 1,TVE 2 (fromList [(0,TInt),(1,TInt)]))
term1 = L "x" (IFZ vx (I 1) (vx :+ (I 2)))
test10 = teval env0 term1
-- (TV 0 :> TInt,TVE 1 (fromList [(0,TInt)]))

test1 = teval env0 term1 -- TInt :> TInt

main = print $ test0

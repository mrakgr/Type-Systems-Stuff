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
type TEnv = Map VarName Typ
data MainEnv = MainEnv {tve :: TVE, tenv :: TEnv}

get_tenv = liftM tenv get
get_tve = liftM tve get
modify_tenv f = modify (\x -> x { tenv = f $ tenv x})
modify_tve f = modify (\x -> x { tve = f $ tve x})

--newtv :: TVE -> (Typ, TVE)
newtv = do
  TVE n s <- get_tve
  modify_tve (const $ TVE (n+1) s)
  return (TV n)

tve0 :: TVE
tve0 = TVE 0 IM.empty

--tvlkup :: TVE -> TVarName -> Maybe Typ
tvlkup v = do
  TVE _ s <- get_tve
  return $ IM.lookup v s

--tvext :: TVE -> (TVarName, Typ) -> TVE
tvext (tv,t) = modify_tve $ \(TVE c s) -> TVE c (IM.insert tv t s)

--tvsub :: TVE -> Typ -> Typ
tvsub (t1 :> t2) = liftM2 (:>) (tvsub t1) (tvsub t2)
tvsub t@(TV v) =
  tvlkup v >>= \case
    Just t' -> tvsub t'
    Nothing -> return t
tvsub t = return t

-- chase through a substitution ‘shallowly’:
-- stop at the last equivalent type variable
--tvchase :: TVE -> Typ -> Typ
tvchase t@(TV v) =
  tvlkup v >>= \case
    Just t' -> tvsub t'
    Nothing -> return t
tvchase t = return t
--
-- If either t1 or t2 are type variables, they must be unbound
unify' TInt TInt = return ()
unify' (t1a :> t1r) (t2a :> t2r) = do
  () <- unify t1r t2r
  () <- unify t1a t2a
  return ()
unify' (TV v1) t2 = unifyv v1 t2
unify' t1 (TV v2) = unifyv v2 t1
unify' t1 t2 = throwError $ Left $ unwords ["constant mismatch:", show t1, show t2]

unifyv v1 (TV v2) | v1 == v2 = return ()
unifyv v1 t2 =
  occurs v1 t2 >>= \case
    True -> do
      m <- tvsub t2
      throwError $ Left $ unwords ["occurs check:", show (TV v1), "in", show m]
    False -> tvext (v1,t2) -- record new constraint

occurs v TInt = return False
occurs v (t1 :> t2) = liftM2 (||) (occurs v t1) (occurs v t2)
occurs v (TV v2) =
  tvlkup v2 >>= \case
    Nothing -> return (v == v2)
    Just t -> occurs v t

unify t1 t2 = do
  t1' <- tvchase t1
  t2' <- tvchase t2
  unify' t1' t2'

lkup x = do
  tenv <- get_tenv
  M.lookup x tenv >>= \case
    Just x -> return x
    Nothing -> return $ throwError $ Left $ "Unbound variable " ++ x
env0 = M.empty
ext k v = modify_tenv (M.insert k v)
--
-- -- teval' :: TEnv -> Term -> TVE -> (Typ,TVE)
-- teval' = \case
--   V x -> lkup x
--   L x e -> do
--     tv <- newtv
--     te <- teval' (ext x tv tenv) e
--     return (tv :> te)
--     A e1 e2 -> do
--       t1 <- teval' tenv e1
--       t2 <- teval' tenv e2
--       t1r <- newtv
--       unify t1 (t2 :> t1r) >>= \case
--         Right tve -> return (t1r,tve)
--         Left err -> error err
--     I n ->
--       return TInt
--     e1 :+ e2 ->
--       let (t1,tve) = teval' tenv e1 tve in
--       let (t2,tve) = teval' tenv e2 tve in
--       case either Left (unify t2 TInt) $  unify t1 TInt tve of
--         Right tve -> (TInt,tve)
--         Left err -> error $ "Trying to add non-integers: " ++ err
--     Fix e ->
--       let (t,tve) = teval' tenv e tve in
--       let (ta,tve) = newtv tve in
--       let (tb,tve) = newtv tve in
--       -- It never occurred to me, but it maybe the `->` type arrows are right associative in ML?
--       case unify t ((ta :> tb) :> ta :> tb) tve of
--         Right tve -> (ta :> tb,tve)
--         Left err -> error $ "Inappropriate type in Fix: " ++ err
--
-- teval :: TEnv -> Term -> Typ
-- teval tenv e =
--   let (t,tve) = teval' tenv e tve0 in
--   tvsub tve t
--
-- (vx,vy) = (V "x", V "y")
-- test0 = teval env0 ((L "x" (vx :+ (I 2))) `A` (I 1))
-- -- (TV 1,TVE 2 (fromList [(0,TInt),(1,TInt)]))
-- term1 = L "x" (IFZ vx (I 1) (vx :+ (I 2)))
-- test10 = teval env0 term1
-- -- (TV 0 :> TInt,TVE 1 (fromList [(0,TInt)]))
--
-- test1 = teval env0 term1 -- TInt :> TInt

-- main = print $ test0
main = return ()

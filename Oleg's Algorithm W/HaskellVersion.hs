-- From http://okmij.org/ftp/Computation/FLOLAC/lecture.pdf
-- Interpreting Types as Abstract Values

{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

import Control.Monad.State.Strict
import Control.Monad.Except

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

data TVE = TVE Int (IntMap Typ) deriving Show
type TEnv = Map VarName Typ
data MainEnv = MainEnv {tve :: TVE, tenv :: TEnv} deriving Show

get_tenv = gets tenv
get_tve = gets tve
modify_tenv f = modify (\x -> x { tenv = f $ tenv x})
modify_tve f = modify (\x -> x { tve = f $ tve x})

newtv = do
  TVE n s <- get_tve
  modify_tve (const $ TVE (n+1) s)
  return (TV n)

tve0 :: TVE
tve0 = TVE 0 IM.empty

tvlkup v = do
  TVE _ s <- get_tve
  return $ IM.lookup v s

tvext (tv,t) = modify_tve $ \(TVE c s) -> TVE c (IM.insert tv t s)

tvsub (t1 :> t2) = liftM2 (:>) (tvsub t1) (tvsub t2)
tvsub t@(TV v) =
  tvlkup v >>= \case
    Just t' -> tvsub t'
    Nothing -> return t
tvsub t = return t

-- chase through a substitution ‘shallowly’:
-- stop at the last equivalent type variable
tvchase t@(TV v) =
  tvlkup v >>= \case
    Just t' -> tvsub t'
    Nothing -> return t
tvchase t = return t

-- If either t1 or t2 are type variables, they must be unbound
unify' TInt TInt = return ()
unify' (t1a :> t1r) (t2a :> t2r) = do
  unify t1r t2r
  unify t1a t2a
unify' (TV v1) t2 = unifyv v1 t2
unify' t1 (TV v2) = unifyv v2 t1
unify' t1 t2 = throwError $ unwords ["constant mismatch:", show t1, "and", show t2]

unifyv v1 (TV v2) | v1 == v2 = return ()
unifyv v1 t2 =
  occurs v1 t2 >>= \case
    True -> do
      m <- tvsub t2
      throwError $ unwords ["occurs check:", show (TV v1), "in", show m]
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
  tenv' <- get_tenv
  case M.lookup x tenv' of
    Just x -> return x
    Nothing -> throwError $ "Unbound variable " ++ x
env0 = M.empty
ext k v = modify_tenv (M.insert k v)

exec_with_backup_tenv f = do
    backup <- get_tenv
    x <- f
    modify_tenv $ const backup
    return x

teval' = \case
  V x -> lkup x
  L x e -> do
    tv <- newtv
    te <- exec_with_backup_tenv $ do
      ext x tv
      teval' e
    return (tv :> te)
  A e1 e2 -> do
    t1 <- teval' e1
    t2 <- teval' e2
    t1r <- newtv
    unify t1 (t2 :> t1r)
    return t1r
  I n ->
    return TInt
  e1 :+ e2 -> do
    t1 <- teval' e1
    t2 <- teval' e2
    unify t1 TInt
    unify t2 TInt
    return TInt
  Fix e -> do
    t <- teval' e
    ta <- newtv
    tb <- newtv
    unify t ((ta :> tb) :> (ta :> tb))
    -- It never occurred to me, but it maybe the `->` type arrows are right associative in ML?
    return (ta :> tb)
  IFZ c tr fa -> do
    t_c <- teval' c
    t_tr <- teval' tr
    t_fa <- teval' fa
    unify t_c TInt
    unify t_tr t_fa
    return t_tr

menv0 = MainEnv {tve = tve0, tenv=env0}

teval0 q e =
  let f = do
        t <- teval' e
        tvsub t in
  case runExcept (runStateT f menv0) of
    Right (x,y) -> q (x,y)
    Left er -> error er

teval e = teval0 fst e

(vx,vy) = (V "x", V "y")
test0 = teval0 id ((L "x" (vx :+ (I 2))) `A` (I 1))
-- (TV 1,TVE 2 (fromList [(0,TInt),(1,TInt)]))
term1 = L "x" (IFZ vx (I 1) (vx :+ (I 2)))
test10 = teval0 id term1
-- (TV 0 :> TInt,TVE 1 (fromList [(0,TInt)]))

test1 = teval term1 -- TInt :> TInt

tmul =
  Fix (L "self" (L "x" (L "y"
    (IFZ vx (I 0)
    (((V "self") `A` (vx :+ (I (-1))) `A` vy) :+ vy)))))

testm21 = teval tmul -- TInt :> TInt :> TInt
testm22 = teval (tmul `A` (I 2)) -- TInt :> TInt
testm23 = teval (tmul `A` (I 2) `A` (I 3)) -- TInt
testm24 = teval (tmul `A` (I (-1)) `A` (I (-1))) -- TInt

term4 = L "x" (IFZ vx (I 1) (vx `A` (I 1)))
test4 = teval term4
-- *** Exception: Trying to compare a non-integer to 0:
-- constant mismatch: TInt :> TV 1 and TInt

delta = L "y" (vy `A` vy)
testd = teval delta
-- *** Exception: occurs check: TV 0 in TV 0 :> TV 1

term2a = L "x" (L "y" (vx `A` vy))
test2a = teval term2a
-- (TV 1 :> TV 2) :> (TV 1 :> TV 2)

termid = L "x" vx
testid = teval termid -- TV 0 :> TV 0

term2id =
  L "f" (L "y"
    ((I 2) :+ ((termid `A` (V "f")) `A` ((termid `A` vy) :+ (I 1)))))
test2id = teval term2id -- (TInt :> TInt) :> (TInt :> TInt)

termlet =
  let c2 = L "f" (L "x" (V "f" `A` (V "f" `A` vx)))
      inc = L "x" (vx :+ (I 1))
      compose = L "f" (L "g" (L "x"
        (V "f" `A` (V "g" `A` vx))))
  in
      c2 `A` (compose `A` inc `A` inc) `A` (I 10) :+
      ((c2 `A` (compose `A` inc) `A` termid) `A` (I 100))
testlet = teval termlet


main = print $ test0

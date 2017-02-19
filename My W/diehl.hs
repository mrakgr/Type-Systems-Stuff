-- From: http://dev.stephendiehl.com/fun/006_hindley_milner.html

{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.Monad
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as M
import Data.Map(Map)
import qualified Data.Set as S
import Data.Set(Set)

-- Syntax

type VarName = String

data Expr
  = Var VarName
  | App Expr Expr
  | Lam VarName Expr
  | Let VarName Expr Expr
  | Lit Lit
  | If Expr Expr Expr
  | Fix Expr
  | Op Binop Expr Expr
  deriving (Show,Eq,Ord)

data Lit
  = LInt Integer
  | LBool Bool
  deriving (Show,Eq,Ord)

data Binop = Add | Sub | Mul | Eql
  deriving (Show,Eq,Ord)

type Decl = (String, Expr)

data Program = Program [Decl] Expr deriving Eq

-- Types

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

newtype TVar = TV Int
  deriving (Eq,Ord)

instance Show TVar where
  show (TV x) = letters !! x

data PrimType
  = TInt
  | TBool
  deriving (Show,Eq,Ord)

infixr 9 :>
data Type
  = TVar TVar
  | TCon PrimType
  | Type :> Type
  deriving (Show,Eq,Ord)

data Scheme = Forall [TVar] Type
newtype TypeEnv = TypeEnv (Map VarName Scheme)

extend (TypeEnv env) (x,s) = TypeEnv $ M.insert x s env

data TypeError
  = UnificationFail Type Type
  | InfiniteType TVar Type
  | UnboundVariable VarName

instance Show TypeError where
  show (UnificationFail t1 t2) = unwords ["unification failed: ", show t1, show t2]
  show (InfiniteType t1 t2) = unwords ["occurs check failed: ", show t1, show t2]

type Unique = Int
type Infer a = ExceptT TypeError (State Unique) a

initUnique = 0

runInfer m closeOver = case evalState (runExceptT m) initUnique of
  Left err -> Left err
  Right res -> Right $ closeOver res

type Subst = Map TVar Type

nullSubst :: Subst
nullSubst = M.empty

compose :: Subst -> Subst -> Subst
compose s1 s2 = M.map (apply s1) s2 `M.union` s1

class Substitutable a where
  apply :: Subst -> a -> a
  ftv :: a -> Set TVar

instance Substitutable Type where
  apply _ (TCon a) = TCon a
  apply s t@(TVar a) = M.findWithDefault t a s
  apply s (t1 :> t2) = apply s t1 :> apply s t2

  ftv (TCon _) = S.empty
  ftv (TVar a) = S.singleton a
  ftv (t1 :> t2) = ftv t1 `S.union` ftv t2

instance Substitutable Scheme where
  apply s (Forall as t) =
    Forall as $ apply s' t where
      -- delete type variables from s
      s' = foldr M.delete s as
  ftv (Forall as t) =
    ftv t `S.difference` S.fromList as

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply
  ftv = foldr (S.union . ftv) S.empty

instance Substitutable TypeEnv where
  apply s (TypeEnv env) = TypeEnv $ M.map (apply s) env
  ftv (TypeEnv env) = ftv $ M.elems env

fresh = do
  s <- get
  put $ s+1
  return $ TVar $ TV s

occursCheck ::  Substitutable a => TVar -> a -> Bool
occursCheck a t = a `S.member` ftv t



unify ::  Type -> Type -> Infer Subst
unify (TCon a) (TCon b) | a == b = return nullSubst
unify (l :> r) (l' :> r') = do
  s1 <- unify l l'
  s2 <- unify r r'
  return (s1 `compose` s2)
unify (TVar v) t = unifyv v t
unify t (TVar v) = unifyv v t
unify t1 t2 = throwError $ UnificationFail t1 t2

unifyv v (TVar t) | v == t = return nullSubst
unifyv v t | occursCheck v t = throwError $ InfiniteType v t
           | otherwise = return $ M.singleton v t

instantiate ::  Scheme -> Infer Type
instantiate (Forall as t) = do
  as' <- mapM (const fresh) as
  let s = M.fromList $ zip as as'
  return $ apply s t

generalize :: TypeEnv -> Type -> Scheme
generalize env t = Forall as t where
  as = S.toList $ ftv t `S.difference` ftv env

lookupEnv :: TypeEnv -> VarName -> Infer (Subst, Type)
lookupEnv (TypeEnv env) x =
  case M.lookup x env of
    Nothing -> throwError $ UnboundVariable x
    Just s -> do
      t <- instantiate s
      return (nullSubst, t)

infer :: TypeEnv -> Expr -> Infer (Subst, Type)
infer env ex = case ex of
  Var x -> lookupEnv env x
  Lam x e -> do
    tv <- fresh
    let env' = env `extend` (x, Forall [] tv)
    (s1, t1) <- infer env' e
    return (s1, apply s1 tv :> t1)
  App e1 e2 -> do
    t1r <- fresh
    (s1,t1) <- infer env e1
    (s2,t2) <- infer (apply s1 env) e2
    s3 <- unify (apply s2 t1) (t2 :> t1r)
    return (s3 `compose` s2 `compose` s1, apply s3 t1r)
  Let x e1 e2 -> do
    (s1,t1) <- infer env e1
    let env' = apply s1 env
        t' = generalize env' t1
    (s2,t2) <- infer (env' `extend` (x,t')) e2
    return (s1 `compose` s2, t2)
  If cond tr fl -> do
    (s1,t1) <- infer env cond
    (s2,t2) <- infer env tr
    (s3,t3) <- infer env fl
    s4 <- unify t1 (TCon TBool)
    s5 <- unify t2 t3
    return (s5 `compose` s4 `compose` s3 `compose` s2 `compose` s1, apply s5 t2)
  Fix e -> do
    (s1,t) <- infer env e
    tv <- fresh
    s2 <- unify (tv :> tv) t
    return (s2, apply s1 tv) -- There is a compose lacking here. This seems like a bug.
  Op op e1 e2 -> do
    (s1,t1) <- infer env e1
    (s2,t2) <- infer env e2
    tv <- fresh
    s3 <- unify (t1 :> t2 :> tv) (ops op)
    return (s1 `compose` s2 `compose` s3, apply s3 tv)
  Lit (LInt _) -> return (nullSubst, TCon TInt)
  Lit (LBool _) -> return (nullSubst, TCon TBool)

typeInt = TCon TInt
typeBool = TCon TBool

ops Add = typeInt :> typeInt :> typeInt
ops Sub = typeInt :> typeInt :> typeInt
ops Mul = typeInt :> typeInt :> typeInt
ops Eql = typeInt :> typeInt :> typeBool


main = return ()

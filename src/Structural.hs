{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Structural where

import Control.Monad.Freer
import Control.Monad.Freer.Error
import Control.Monad.Freer.State
import Data.Coerce

-- Bounded reuse.

data Term
  = Int Int
  | Add Term Term
  | Var Int
  | Abs Type Term
  | App Term Term
  deriving (Eq, Show)

data Type
  = IntType
  | Fun Type Scalar Type
  deriving (Eq, Show)

newtype Scalar = Scalar { getScalar :: Int }
  deriving (Eq, Show)

inc :: Scalar -> Scalar
inc (Scalar n) = Scalar $ n + 1

newtype Context = Context { getContext :: [(Type, Scalar)] }
  deriving (Eq, Show)

add :: (Type, Scalar) -> Context -> Context
add p (Context xs) = Context $ p : xs

update :: Int -> (Type, Scalar) -> Context -> Context
update 0 p (Context (_ : xs)) = Context $ p : xs
update n p (Context (x : xs)) = coerce (x: ) $ update (n - 1) p $ Context xs

nth :: Members '[Error TypeError] r => Int -> Context -> Eff r (Type, Scalar)
nth n (Context xs)
  | 0 <= n && n < length xs = return $ xs !! n
  | otherwise               = throwError $ UnboundVariable n

use :: Members '[State Context, Error TypeError] r => Int -> Eff r Type
use n = do
  ctx <- get
  (ty, s) <- nth n ctx
  put $ update n (ty, inc s) ctx
  return ty

pop :: Members '[State Context, Error TypeError] r => Eff r (Type, Scalar)
pop = do
  Context xs <- get
  case xs of
    [] -> error "pop: unexpected error"
    y : ys -> do
      put $ Context ys
      return y

mul :: Members '[State Context] r => Scalar -> Context -> Eff r ()
mul (Scalar n) (Context xs) = modify $ f xs
  where
    f :: [(Type, Scalar)] -> Context -> Context
    f _ (Context []) = Context []
    f (p : ps) (Context (y : ys)) = coerce (mul' n p y :) $ f ps $ Context ys
    f _ _ = error "mul: unexpected error"

mul' :: Int -> (Type, Scalar) -> (Type, Scalar) -> (Type, Scalar)
mul' n (ty, Scalar m1) (_, Scalar m2) = (ty, Scalar $ m1 + (m2 - m1) * n)

data TypeError
  = UnboundVariable Int
  | TypeMismatch Type Type
  | NotFunction Type
  deriving (Eq, Show)

expect :: Member (Error TypeError) r => Type -> Type -> Eff r ()
expect ty1 ty2
  | ty1 == ty2 = return ()
  | otherwise = throwError $ TypeMismatch ty1 ty2

typeOf :: Members '[State Context, Error TypeError] r => Term -> Eff r Type
typeOf (Int _) = return IntType
typeOf (Add t1 t2) = do
  typeOf t1 >>= expect IntType
  typeOf t2 >>= expect IntType
  return IntType
typeOf (Var n) = use n
typeOf (Abs ty t) = do
  modify $ add (ty, Scalar 0)
  ty' <- typeOf t
  s <- snd <$> pop
  return $ Fun ty s ty'
typeOf (App t1 t2) = do
  ty1 <- typeOf t1
  ctx <- get
  ty2 <- typeOf t2
  case ty1 of
    Fun ty11 s ty12
      | ty11 == ty2 -> do
          mul s ctx
          return ty12
      | otherwise -> throwError $ TypeMismatch ty11 ty2
    _ -> throwError $ NotFunction ty1

typecheck :: Context -> Term -> Either TypeError (Type, Context)
typecheck ctx t = run $ runError $ runState ctx $ typeOf t

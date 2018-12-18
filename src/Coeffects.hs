{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Coeffects where

import Control.Monad.Freer
import Control.Monad.Freer.Error
import Control.Monad.Freer.Reader

-- Liveness analysis.

data Term
  = Var Int
  | Abs Type Term
  | App Term Term
  | Int Int
  deriving (Eq, Show)

data Type
  = IntType
  | Fun (Liveness Type) Type
  deriving (Eq, Show)

data Liveness a
  = L a
  | D a
  deriving (Eq, Show)

fromLiveness :: Liveness a -> a
fromLiveness (L x) = x
fromLiveness (D x) = x

emp :: a -> Liveness a
emp = L

constant :: a -> Liveness a
constant = D

joins :: Liveness a -> Liveness b -> c -> Liveness c
joins (D _) (D _) = D
joins _     _     = L

plus :: Liveness a -> Liveness b -> c -> Liveness c
plus (L _) (L _) = L
plus _     _     = D

newtype Context = Context { getContext :: [Type]}
  deriving (Eq, Show)

add :: Type -> Context -> Context
add ty (Context xs) = Context $ ty : xs

data TypeError
  = UnboundVariable Int
  | TypeMismatch Type Type
  | NotFunction Type
  deriving (Eq, Show)

get :: Members '[Reader Context, Error TypeError] r => Int -> Eff r Type
get n = asks getContext >>= f
  where
    f :: Members '[Reader Context, Error TypeError] r => [Type] -> Eff r Type
    f xs
      | 0 <= n && n < length xs = return $ xs !! n
      | otherwise               = throwError $ UnboundVariable n

typeOf :: Members '[Reader Context, Error TypeError] r => Term -> Eff r (Liveness Type)
typeOf (Int _) = return $ D IntType
typeOf (Var n) = L <$> get n
typeOf (Abs ty t) = do
  lt <- local (add ty) $ typeOf t
  case lt of
    L x -> return $ L $ Fun (L ty) x
    D x -> return $ D $ Fun (D ty) x
typeOf (App t1 t2) = do
  lt1 <- typeOf t1
  lt2 <- typeOf t2
  case fromLiveness lt1 of
    Fun lt11 ty12
      | fromLiveness lt11 == fromLiveness lt2 -> return $ joins lt1 (plus lt2 lt11 ()) ty12
      | otherwise                             -> throwError $ TypeMismatch (fromLiveness lt11) (fromLiveness lt2)
    ty -> throwError $ NotFunction ty

typecheck :: Context -> Term -> Either TypeError (Liveness Type)
typecheck ctx t = run $ runError $ runReader ctx $ typeOf t

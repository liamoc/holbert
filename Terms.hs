{-# LANGUAGE FlexibleContexts #-}
module Terms 
  ( Term (..), Masked (..), Id
  , raise, raise'
  , isUsed
  , subst
  , substMV
  , reduce
  , peelApTelescope, applyApTelescope
  , Subst, applySubst, fromUnifier
  , invalidName
  ) where

import qualified Data.Map as M
import Data.String
import Data.List (foldl')
import Data.Char (isSpace)

-- Judge equality of terms modulo alpha equivalence.
-- we do this by hiding names from the Eq instance.
type Id = String 
newtype Masked a = M a 
instance Eq (Masked a) where 
   _ == _ = True 
instance Show a => Show (Masked a) where
  show (M a) = show a
instance Ord (Masked a) where
  compare _ _ = EQ
instance IsString a => IsString (Masked a) where
  fromString = M . fromString

type Index = Int
data Term = LocalVar Index
          | MetaVar Id
          | Ap Term Term
          | Const String
          | Lam (Masked Id) Term
          deriving (Show, Eq, Ord)

invalidName "" = Just "Name cannot be empty"
invalidName s | any isSpace s = Just "Name contains spaces"
invalidName s | any (`elem` ("()." :: String)) s = Just "Name contains reserved symbols"
invalidName s = Nothing

raise :: Int -> Term -> Term
raise = raise' 0

raise' :: Int -> Int -> Term -> Term
raise' lower i t = case t of
   LocalVar j -> if j >= lower then LocalVar (i + j) else LocalVar j
   MetaVar i -> MetaVar i
   Const s -> Const s
   Ap l r -> raise' lower i l `Ap` raise' lower i r
   Lam n body -> Lam n (raise' (lower + 1) i body)

isUsed :: Int -> Term -> Bool
isUsed i (LocalVar j) = i == j
isUsed i (Lam _ t) = isUsed (i+1) t
isUsed i (Ap t u)  = isUsed i t || isUsed i u
isUsed i _ = False


subst :: Term -> Int -> Term -> Term
subst new i t = case t of
  LocalVar j -> case compare j i of
    LT -> LocalVar j
    EQ -> new
    GT -> LocalVar (j - 1)
  MetaVar i -> MetaVar i
  Ap l r -> subst new i l `Ap` subst new i r
  Const s -> Const s
  Lam n body -> Lam n (subst (raise 1 new) (i + 1) body)

substMV :: Term -> Id -> Term -> Term
substMV new i t = case t of
  LocalVar i -> LocalVar i
  MetaVar j  -> if i == j then new else MetaVar j
  Ap l r     -> substMV new i l `Ap` substMV new i r
  Const s    -> Const s
  -- This raising should not be strictly necessary as metavariables should not be subbed for open terms
  Lam n body -> Lam n (substMV (raise 1 new) i body)

reduce :: Term -> Term
reduce t = case t of
  LocalVar j -> LocalVar j
  MetaVar i -> MetaVar i
  Const i -> Const i
  Ap l r -> case reduce l of
    Lam n body -> reduce (subst r 0 body)
    l' -> Ap l' (reduce r)
  Lam n body -> Lam n (reduce body)

peelApTelescope :: Term -> (Term, [Term])
peelApTelescope t = go t []
  where go (Ap f r) rest = go f (r : rest)
        go t rest = (t, rest)

applyApTelescope :: Term -> [Term] -> Term
applyApTelescope = foldl' Ap

newtype Subst = S (M.Map Id Term)
instance Semigroup Subst where
  S s1 <> S s2 | not (M.null (M.intersection s1 s2)) = error "Impossible"
               | otherwise = S $ M.union (applySubst (S s1) <$> s2) (applySubst (S s2) <$> s1)
instance Monoid Subst where
  mempty = S (M.empty)

applySubst :: Subst -> Term -> Term
applySubst (S s) t = reduce $ M.foldrWithKey (\mv sol t -> substMV sol mv t) t s

fromUnifier :: [(String,Term)] -> Subst
fromUnifier [] = mempty
fromUnifier ((x,v):ts) = let S s = fromUnifier ts
                          in S $ M.insert x v (substMV v x <$> s)

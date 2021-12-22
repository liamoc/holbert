{-# LANGUAGE FlexibleContexts, OverloadedStrings #-}
module Unification (unifier, fresh, UnifyM, runUnifyM, UnifyError) where
import qualified Miso.String as MS
import Control.Monad
import Control.Monad.State
import Control.Monad.Trans
import Control.Monad.Except
import qualified Data.Map.Strict     as M
import Data.Maybe
import Data.Foldable
import qualified Data.Set            as S

import Terms

-- almost all of this is a direct port of Tobias Nipkow's pattern unification implementation
-- in standard ML.
type UnifyError = MS.MisoString

gen = do x <- get; put (x + 1); pure x

lams (x:xs) t = Lam (M "x") (lams xs t)
lams [] t = t

hnf xs f ss = lams xs (applyApTelescope f ss)

occ f sS (MetaVar g) = (f == g)  || (case lookup g sS of
                                      Just s -> occ f sS s
                                      Nothing -> False)
occ f sS (Ap s t) = occ f sS s || occ f sS t
occ f sS (Lam _ t) = occ f sS t
occ f sS _ = False


mapbnd f = let mpb d (LocalVar i) = LocalVar (if i<d then i else f(i-d)+d)
               mpb d (Lam n t) = Lam n (mpb (d+1) t)
               mpb d (Ap u1 u2) = Ap (mpb d u1) (mpb d u2)
               mpb d t = t
            in mpb 0

incr = mapbnd (+1)

red (Lam _ s) (LocalVar i : bs) js = red s bs (i:js)
red s         bs                js = applyApTelescope (mapbnd (js !!) s) bs;

devar sS s | (MetaVar f, is) <- peelApTelescope s
           , Just t <- lookup f sS = devar sS (red t is [])
devar sS s = s

pos :: (a -> Bool) -> [a] -> [Term]
pos p (x:xs) = if p x then LocalVar(length xs) : pos p xs else pos p xs
pos p [] = []

posM p (x:xs) = do c <- p x; if c then (LocalVar(length xs):) <$>  posM p xs else posM p xs
posM p [] = pure []
idx (b:bs) b' = if b==b' then LocalVar(length bs) else idx bs b'
idx [] _ = LocalVar(-10000)


fresh = MetaVar <$> lift gen

proj sS s = case peelApTelescope (devar sS s) of
        (Lam _ t,_) -> proj sS t
        (Const _,ss) -> foldlM proj sS ss
        (LocalVar i,ss) | i >= 0 -> foldlM proj sS ss
                        | otherwise -> throwError "Unification Failure i < 0"
        (MetaVar f,bs) -> do
           var <- fresh
           bs' <- posM ( \ t -> case t of (LocalVar i) -> pure (i >= 0)
                                          otherthing  -> throwError "Non-pattern equation" ) bs
           pure ((f , hnf bs var bs' ):sS)


flexflex1 f ym zn sS
    | ym == zn =  pure $ sS
    | otherwise = do
       var <- fresh
       pure ((f, hnf ym var (pos (uncurry (==)) (zip ym zn))) : sS)


subset :: (Eq a) => [a] -> [a] -> Bool
subset as bs = all (`elem` bs) as

intersection :: (Eq a) => [a] -> [a] -> [a]
intersection xs ys = filter (`elem` ys) xs

flexflex2 f im g jn sS
    | im `subset` jn = pure $ ((g, lam' jn (MetaVar f) im) : sS )
    | jn `subset` im = pure $ ((f, lam' im (MetaVar g) jn) : sS)
    | otherwise = do
         let kl = im `intersection` jn
         h <- fresh
         pure ((f, lam' im h kl ) : (g, lam' jn h kl ) : sS)
  where
    lam' im g jn = hnf im g (map (idx im) jn)


flexflex f ym g zn sS
  | f == g = flexflex1 f ym zn sS
  | otherwise = flexflex2 f ym g zn sS

flexrigid f im t sS
  | occ f sS t = throwError "Unification failure (occurs check)"
  | otherwise  = let u = mapbnd (\i -> let (LocalVar n) = idx im (LocalVar i) in n) t
                  in proj((f,lams im u):sS) u

unif sS (s,t) = case (devar sS s,devar sS t) of
        (Lam _ s, Lam _ t) -> unif sS (s,t)
        (Lam _ s,t) -> unif sS (s, Ap (incr t) (LocalVar 0))
        (s,Lam _ t) -> unif sS (Ap (incr s) (LocalVar 0), t)
        (s,t) -> cases sS (s,t)

cases sS (s,t) = case (peelApTelescope s,peelApTelescope t) of
        ((MetaVar f,ym),(MetaVar g,zn)) -> flexflex f ym g zn sS
        ((MetaVar f,ym),_) -> flexrigid f ym t sS
        (_,(MetaVar f,ym)) -> flexrigid f ym s sS
        ((a,sm),(b,tn)) -> rigidrigid a sm b tn sS

rigidrigid a ss b ts sS
  | a == b, length ss == length ts  = foldlM unif sS (zip ss ts)
  | otherwise = throwError (MS.toMisoString (concat ["Unification Error (", show a, ", ", show b, ")"])) --"Unification Error (rigid, rigid)"

type Gen = State Int

type UnifyM = ExceptT MS.MisoString (State Int)

unifier :: Term-> Term -> UnifyM Subst
unifier t1 t2 = fromUnifier <$> unif [] (t1,t2)


runUnifyM = runState . runExceptT

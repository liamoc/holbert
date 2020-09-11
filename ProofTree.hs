{-# LANGUAGE TupleSections, FlexibleContexts, GADTs, DeriveGeneric, DeriveAnyClass #-}
module ProofTree where

import Data.Maybe
import Data.List
import Control.Monad
import Control.Monad.Writer (WriterT (..), tell)
import Control.Monad.Trans (lift)
import GHC.Generics(Generic)
import Data.Aeson (ToJSON,FromJSON)
import qualified Prop as P
import qualified Terms as T
import StringRep
import Unification
import Optics.Core

data ProofTree = PT [T.Name] [P.Prop] T.Term (Maybe (P.RuleRef, [ProofTree]))
               deriving (Eq, Show, Generic, ToJSON, FromJSON)

type Path = [Int]

data Context = Context { bound :: [T.Name], locals :: [P.Prop] } deriving (Show)

instance Semigroup Context where
  Context bs lcls <> Context bs' lcls' = Context (bs' ++ bs) (map (P.raise (length bs')) lcls ++ lcls')
instance Monoid Context where
  mempty = Context [] []

infixl 9 %+
(%+) a b = icompose (<>) (a % b)

subgoals :: IxAffineTraversal' Context ProofTree [ProofTree]
subgoals = step % _Just % _2

subgoal :: Int -> IxAffineTraversal' Context ProofTree ProofTree
subgoal n = subgoals % ix n

step :: IxLens' Context ProofTree (Maybe (P.RuleRef, [ProofTree]))
step = ilens (\(PT xs lcls t sg) -> (Context (reverse xs) lcls, sg))
             (\(PT xs lcls t _ ) sg -> PT xs lcls t sg)

path :: [Int] -> IxAffineTraversal' Context ProofTree ProofTree
path [] = iatraversal (Right . (mempty,)) (const id)
path (x:xs) = path xs %+ subgoal x

assumptions :: Lens' ProofTree [P.Prop]
assumptions = lens (\(PT _  lcls _ _ ) -> lcls)
                   (\(PT xs _    t sg) lcls -> PT xs lcls t sg)

inference :: IxLens' Context ProofTree T.Term
inference = ilens (\(PT xs lcls t _ ) -> (Context (reverse xs) lcls, t))
                  (\(PT xs lcls _ sg) t -> PT xs lcls t sg)

goalbinders :: Lens' ProofTree [T.Name]
goalbinders = lens (\(PT xs _   _ sg) -> xs)
                   (\(PT _ lcls t sg) xs -> PT xs lcls t sg)



fromProp :: P.Prop -> ProofTree
fromProp (P.Forall sks lcls g) = PT sks lcls g Nothing

dependencies :: Traversal' ProofTree P.RuleName
dependencies = traversalVL guts
  where
    guts act (PT sks lcls g (Just (P.Defn rr,sgs)))
        = (\rr' sgs' -> PT sks lcls g (Just (P.Defn rr',sgs')))
          <$> act rr
          <*> traverse (guts act) sgs
    guts act x = pure x


outstandingGoals :: IxTraversal' Path ProofTree ProofTree
outstandingGoals = itraversalVL (\act -> guts act [])
  where
    guts act pth (PT sks lcls g (Just (rr,sgs)))
        = (\sgs' -> PT sks lcls g (Just (rr,sgs')))
          <$> traverse (uncurry $ guts act) (zip (map (:pth) [0..]) sgs)
    guts act pth p@(PT sks lcls g Nothing) = act pth p

apply :: P.NamedProp -> Path -> ProofTree -> UnifyM ProofTree
apply (r,prp) p pt = do
    do (pt', subst) <- runWriterT $ iatraverseOf (path p) pure guts pt
       pure $ applySubst subst pt'
  where
    guts :: Context -> ProofTree -> WriterT T.Subst UnifyM ProofTree
    guts context (PT xs lcls t _) = do
       (subst, sgs) <- lift $ applyRule (reverse xs ++ bound context) t prp
       tell subst
       pure $ PT xs lcls t (Just (r,sgs))

    applyRule :: [T.Name] -> T.Term -> P.Prop -> UnifyM (T.Subst, [ProofTree])
    applyRule skolems g (P.Forall (m :ms) sgs g') = do
       n <- fresh
       let mt = foldl T.Ap n (map T.LocalVar [0..length skolems -1])
       applyRule skolems g (P.subst mt 0 (P.Forall ms sgs g'))
    applyRule skolems g (P.Forall [] sgs g') = do
       (,map fromProp sgs) <$> unifier g g'

applySubst :: T.Subst -> ProofTree -> ProofTree
applySubst subst (PT sks lcls g sgs) =
    PT sks (map (P.applySubst subst) lcls) (T.applySubst subst g) (fmap (fmap (map (applySubst subst))) sgs)

clear :: P.RuleName -> ProofTree -> ProofTree
clear toClear x@(PT sks lcl g (Just (rr,sgs)))
     | rr == (P.Defn toClear) = PT sks lcl g Nothing
     | otherwise              = PT sks lcl g $ Just (rr, map (clear toClear) sgs)
clear toClear x = x


renameRule :: (P.RuleName, P.RuleName) -> ProofTree -> ProofTree
renameRule (s,s') pt = over dependencies subst pt
  where
    subst n = if n == s then s' else n

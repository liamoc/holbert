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
import qualified Miso.String as MS
import StringRep
import Unification
import Optics.Core

data ProofDisplayData = PDD { proseStyle :: Bool, subtitle :: MS.MisoString} 
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

data ProofTree = PT (Maybe ProofDisplayData) [T.Name] [P.Prop] T.Term (Maybe (P.RuleRef, [ProofTree]))
               deriving (Eq, Show, Generic, ToJSON,FromJSON)


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
step = ilens (\(PT _ xs lcls t sg) -> (Context (reverse xs) lcls, sg))
             (\(PT opts xs lcls t _ ) sg -> PT opts xs lcls t sg)

path :: [Int] -> IxAffineTraversal' Context ProofTree ProofTree
path [] = iatraversal (Right . (mempty,)) (const id)
path (x:xs) = path xs %+ subgoal x

style :: Lens' ProofTree (Maybe ProofDisplayData)
style = lens (\(PT opts _  _ _ _ ) -> opts)
             (\(PT _ xs lcls t sg) opts -> PT opts xs lcls t sg)

assumptions :: Lens' ProofTree [P.Prop]
assumptions = lens (\(PT _    _  lcls _ _ ) -> lcls)
                   (\(PT opts xs _    t sg) lcls -> PT opts xs lcls t sg)

inference :: IxLens' Context ProofTree T.Term
inference = ilens (\(PT _ xs lcls t _ ) -> (Context (reverse xs) lcls, t))
                  (\(PT opts xs lcls _ sg) t -> PT opts xs lcls t sg)

goalbinders :: Lens' ProofTree [T.Name]
goalbinders = lens (\(PT _ xs _   _ sg) -> xs)
                   (\(PT opts _ lcls t sg) xs -> PT opts xs lcls t sg)



fromProp :: P.Prop -> ProofTree
fromProp (P.Forall sks lcls g) = PT Nothing sks lcls g Nothing

dependencies :: Traversal' ProofTree P.RuleName
dependencies = traversalVL guts
  where
    guts act (PT opts sks lcls g (Just (P.Defn rr,sgs)))
        = (\rr' sgs' -> PT opts sks lcls g (Just (P.Defn rr',sgs')))
          <$> act rr
          <*> traverse (guts act) sgs
    guts act x = pure x


outstandingGoals :: IxTraversal' Path ProofTree ProofTree
outstandingGoals = itraversalVL (\act -> guts act [])
  where
    guts act pth (PT opts sks lcls g (Just (rr,sgs)))
        = (\sgs' -> PT opts sks lcls g (Just (rr,sgs')))
          <$> traverse (uncurry $ guts act) (zip (map (:pth) [0..]) sgs)
    guts act pth p@(PT opts sks lcls g Nothing) = act pth p

apply :: P.NamedProp -> Path -> ProofTree -> UnifyM ProofTree
apply (r,prp) p pt = do
    do (pt', subst) <- runWriterT $ iatraverseOf (path p) pure guts pt
       pure $ applySubst subst pt'
  where
    guts :: Context -> ProofTree -> WriterT T.Subst UnifyM ProofTree
    guts context (PT opts xs lcls t _) = do
       (subst, sgs) <- lift $ applyRule (reverse xs ++ bound context) t prp
       tell subst
       pure $ PT opts xs lcls t (Just (r,sgs))

    applyRule :: [T.Name] -> T.Term -> P.Prop -> UnifyM (T.Subst, [ProofTree])
    applyRule skolems g (P.Forall (m :ms) sgs g') = do
       n <- fresh
       let mt = foldl T.Ap n (map T.LocalVar [0..length skolems -1])
       applyRule skolems g (P.subst mt 0 (P.Forall ms sgs g'))
    applyRule skolems g (P.Forall [] sgs g') = do
       (,map fromProp sgs) <$> unifier g g'

    -- Identical to applyRule(Intro) but also tries to unifie with an assumption
    -- Will only try to unify goal if it usinifies with an assumption
    applyRuleElim :: [T.Name] ->  [T.Prop] -> T.Term -> P.Prop -> UnifyM (T.Subst, [ProofTree]) -- added [T.Prop] for assumptions
    applyRuleElim skolems assmps g (P.Forall (m:ms) sgs g') = do  -- skolem is in scope; is bound and can't be subsituted - can't unify with these vars
       n <- fresh  -- Returns increasing #, always unique
       let mt = foldl T.Ap n (map T.LocalVar [0..length skolems - 1])  -- de Bruijn indexing: indices refers to every var inscope by its bound pos, T.Ap x y - application: expr subst
       applyRuleElim skolems assmps g (P.subst mt 0 (P.Forall ms sgs g'))
    applyRuleElim skolems (a:assmps) g (P.Forall [] (s:sgs) g') = (do
       substs <- unifierProp a s
       (,map fromProp sgs) <$> unifier (T.applySubst substs g) (T.applySubst substs g'))  -- T.applySubst like P.subst but takes terms not props
       <|> applyRuleElim skolems assmps g (P.Forall [] (s:sgs) g')  -- <|> := else
    applyRuleElim skolems [] g (P.Forall [] sgs g') = empty
    applyRuleElim skolems assmps g (P.subst mt 0 (P.Forall [] [] g')) = g

applySubst :: T.Subst -> ProofTree -> ProofTree
applySubst subst (PT opts sks lcls g sgs) =
    PT opts sks (map (P.applySubst subst) lcls) (T.applySubst subst g) (fmap (fmap (map (applySubst subst))) sgs)

clear :: P.RuleName -> ProofTree -> ProofTree
clear toClear x@(PT opts sks lcl g (Just (rr,sgs)))
     | rr == (P.Defn toClear) = PT opts sks lcl g Nothing
     | otherwise              = PT opts sks lcl g $ Just (rr, map (clear toClear) sgs)
clear toClear x = x


renameRule :: (P.RuleName, P.RuleName) -> ProofTree -> ProofTree
renameRule (s,s') pt = over dependencies subst pt
  where
    subst n = if n == s then s' else n

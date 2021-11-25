{-# LANGUAGE TupleSections, FlexibleContexts, GADTs, DeriveGeneric, DeriveAnyClass, OverloadedStrings #-}
module ProofTree where

import Data.Maybe
import Data.List
import Control.Applicative
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

data Style = Tree | Prose | Equational deriving (Eq, Show, Generic, ToJSON, FromJSON)

data ProofDisplayData = PDD { proofStyle :: Style, subtitle :: MS.MisoString} 
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

toggleStyle :: Style -> Style
toggleStyle Tree = Prose
toggleStyle Prose = Tree
toggleStyle Equational = Tree



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
    
    guts act (PT opts sks lcls g (Just (P.Rewrite (P.Defn rr),sgs)))
        = (\rr' sgs' -> PT opts sks lcls g (Just (P.Rewrite (P.Defn rr'),sgs')))
          <$> act rr
          <*> traverse (guts act) sgs
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

applyRewrite :: P.NamedProp -> Bool -> Path -> ProofTree -> UnifyM ProofTree
applyRewrite (r,prp) shouldReverse p pt = do
    do (pt', subst) <- runWriterT $ iatraverseOf (path p) pure guts pt
       pure $ applySubst subst pt'
  where
    guts :: Context -> ProofTree -> WriterT T.Subst UnifyM ProofTree
    guts context (PT d xs lcls t _) = do
       (subst, r, sgs) <- lift $ applyEq (reverse xs ++ bound context) shouldReverse t (r,prp)
       tell subst
       pure $ PT d xs lcls t (Just (r,sgs))

applyEq :: [T.Name] -> Bool -> T.Term -> P.NamedProp -> UnifyM (T.Subst, P.RuleRef, [ProofTree])
applyEq skolems shouldReverse g (r,(P.Forall (m :ms) sgs g')) = do
  n <- fresh
  let mt = foldl T.Ap n (map T.LocalVar [0..length skolems -1])
  applyEq skolems shouldReverse g (r,(P.subst mt 0 (P.Forall ms sgs g')))
applyEq skolems shouldReverse g (r,(P.Forall [] sgs g')) = do
  (s,t) <- match skolems g (P.Forall [] sgs g')
  return (s,P.Rewrite r,((PT Nothing [] [] t Nothing):(map fromProp sgs)))
  where
    match :: [T.Name] -> T.Term -> P.Prop -> UnifyM (T.Subst, T.Term)
    match skolems  g (P.Forall _ sgs g') = (do
      a <- fresh
      let ma = foldl T.Ap a (map T.LocalVar [0..length skolems -1])
      s <- if shouldReverse then unifier g' (T.Ap (T.Ap (T.Const "_=_") ma) g) else unifier g' (T.Ap (T.Ap (T.Const "_=_") g) ma)
      return (s, ma)) <|> case g of
        (T.Lam (T.M x) e) -> do
          (a,b) <- match (x:skolems) e (P.Forall [] sgs g')
          return (a, (T.Lam (T.M x) b))
        (T.Ap e1 e2) -> (do
          (a,b) <- match skolems e1 (P.Forall [] sgs g')
          return (a, (T.Ap b e2))) <|> do
            (a,b) <- match skolems e2 (P.Forall [] sgs g')
            return (a, (T.Ap e1 b))
        otherwise -> empty

applySubst :: T.Subst -> ProofTree -> ProofTree
applySubst subst (PT opts sks lcls g sgs) =
    PT opts sks (map (P.applySubst subst) lcls) (T.applySubst subst g) (fmap (fmap (map (applySubst subst))) sgs)

clear :: P.RuleName -> ProofTree -> ProofTree
clear toClear x@(PT opts sks lcl g (Just (rr,sgs)))
     | rr == (P.Defn toClear) = PT opts sks lcl g Nothing
     | rr == (P.Rewrite (P.Defn toClear)) = PT opts sks lcl g Nothing
     | otherwise              = PT opts sks lcl g $ Just (rr, map (clear toClear) sgs)
clear toClear x = x


renameRule :: (P.RuleName, P.RuleName) -> ProofTree -> ProofTree
renameRule (s,s') pt = over dependencies subst pt
  where
    subst n = if n == s then s' else n

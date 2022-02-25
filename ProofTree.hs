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
import Control.Applicative

--data Style = Tree | Prose | Equational

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

--nextStyle :: Style -> Style
--nextStyle Tree = Prose
--nextStyle Prose = Equational
--nextStyle Equational = Tree

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
    
    guts act (PT opts sks lcls g (Just (P.Rewrite (P.Defn rr) fl,sgs)))
        = (\rr' sgs' -> PT opts sks lcls g (Just (P.Rewrite (P.Defn rr') fl,sgs')))
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
  return (s,P.Rewrite r shouldReverse,((PT Nothing [] [] t Nothing):(map fromProp sgs)))
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

-- Wrapper for elim rules
-- Rule to apply, path to apply it to, which assumption to apply elim to
applyElim :: P.NamedProp -> Path -> P.NamedProp -> ProofTree -> UnifyM ProofTree
applyElim (r,prp) p (rr,assm) pt = do
    do (pt', subst) <- runWriterT $ iatraverseOf (path p) pure guts pt
       pure $ applySubst subst pt'
  where
    guts :: Context -> ProofTree -> WriterT T.Subst UnifyM ProofTree
    guts context (PT opts xs lcls t _) = do
       (subst, sgs) <- lift $ applyRuleElim (reverse xs ++ bound context) t prp  -- Get assumption from context (is bound context correct?)
       tell subst
       pure $ PT opts xs lcls t (Just (P.Elim r rr,sgs))

    -- Identical to applyRule (for Intro) above but also tries to unify with an assumption
    -- Will only try to unify goal if it unifies with an assumption
    applyRuleElim :: [T.Name] -> T.Term -> P.Prop -> UnifyM (T.Subst, [ProofTree])
    applyRuleElim skolems g r@(P.Forall ms (P.Forall [] [] t:sgs) g') = do  -- m:ms will change to list of specific vars
        let indices = T.mentioned t
        (result,_) <- foldM (\(r,count) i -> (,) <$> generalise skolems (i-count) r <*> pure (count+1) ) (r,0) (sort indices)
        let (P.Forall ms' (s:sgs') g') = result
        substs <- P.unifierProp (P.raise (length ms') assm) s
        -- apply substs to our rule
        let introRule = P.applySubst substs (P.Forall ms' sgs' g')
        -- applyRule to the result on our goal
        (substs', sgs'') <- applyRule skolems g introRule
        pure (substs <> substs', sgs'')
    applyRuleElim skolems g _ = empty
    
    applyRule :: [T.Name] -> T.Term -> P.Prop -> UnifyM (T.Subst, [ProofTree])
    applyRule skolems g (P.Forall (m :ms) sgs g')
      | (T.LocalVar 0,args) <- T.peelApTelescope g' = do
         let cutoff = length (m:ms) 
         let exclusions = map (subtract cutoff) $ filter (>= cutoff) $ concatMap T.mentioned args 
         n <- fresh
         let mt = foldl T.Ap n (map T.LocalVar $ filter (`notElem` exclusions) $ [0..length skolems -1])
         applyRule skolems g (P.subst mt 0 (P.Forall ms sgs g')) 
      | otherwise = do
         n <- fresh
         let mt = foldl T.Ap n (map T.LocalVar [0..length skolems -1])
         applyRule skolems g (P.subst mt 0 (P.Forall ms sgs g'))
    applyRule skolems g (P.Forall [] sgs g') = do
       (,map fromProp sgs) <$> unifier g g'


-- generlaise func to apply to all the mentioned (terms.hs)
-- generalise :: [Vars in scope] -> Prop -> Index -> Prop (unnified?)
-- 1: get all mentioned of A_1 in x
-- 2: generlaise with 1
-- 3: unify A_1 with chosen assumps in elim rule
-- 4: 

generalise :: [T.Name] -> T.Index -> P.Prop -> UnifyM P.Prop
generalise skolems i r@(P.Forall ms sgs g) = do 
    let (outer,_:inner) = splitAt (length ms - i - 1) ms
    n <- fresh  -- Returns increasing #, always unique
    let mt = foldl T.Ap n (map T.LocalVar [0+length outer..length skolems - 1 + length outer])  
    let (P.Forall inner' sgs' g') = (P.subst mt 0 (P.Forall inner sgs g))
    pure (P.Forall (outer++inner') sgs' g')
    

applySubst :: T.Subst -> ProofTree -> ProofTree
applySubst subst (PT opts sks lcls g sgs) =
    PT opts sks (map (P.applySubst subst) lcls) (T.applySubst subst g) (fmap (fmap (map (applySubst subst))) sgs)

clear :: P.RuleName -> ProofTree -> ProofTree
clear toClear x@(PT opts sks lcl g (Just (rr,sgs)))
     | rr == (P.Defn toClear) = PT opts sks lcl g Nothing
     | rr == (P.Rewrite (P.Defn toClear) True) = PT opts sks lcl g Nothing
     | rr == (P.Rewrite (P.Defn toClear) False) = PT opts sks lcl g Nothing
     | otherwise              = PT opts sks lcl g $ Just (rr, map (clear toClear) sgs)
clear toClear x = x


renameRule :: (P.RuleName, P.RuleName) -> ProofTree -> ProofTree
renameRule (s,s') pt = over dependencies subst pt
  where
    subst n = if n == s then s' else n

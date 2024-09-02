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
import Data.Char (isDigit)
import Debug.Trace 

data ProofStyle = Tree | Prose | Calc | Abbr
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

data ProofDisplayData = PDD { style :: ProofStyle, subtitle :: MS.MisoString} 
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

displaydata :: Lens' ProofTree (Maybe ProofDisplayData)
displaydata = lens (\(PT opts _  _ _ _ ) -> opts)
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


ruleRefs :: Traversal' ProofTree P.RuleRef
ruleRefs = traversalVL guts
  where
    guts act (PT opts sks lcls g (Just (rr,sgs)))
        = (\rr' sgs' -> PT opts sks lcls g (Just (rr',sgs')))
          <$> act rr
          <*> traverse (guts act) sgs
    guts act x = pure x

dependencies :: Traversal' ProofTree P.RuleName
dependencies = traversalVL guts
  where
    guts act (PT opts sks lcls g (Just (P.Elim (P.Defn rr) rr2,sgs)))
        = (\rr' sgs' -> PT opts sks lcls g (Just (P.Elim (P.Defn rr') rr2,sgs')))
          <$> act rr
          <*> traverse (guts act) sgs
    
    guts act (PT opts sks lcls g (Just (P.Rewrite (P.Defn rr) fl cl,sgs)))
        = (\rr' sgs' -> PT opts sks lcls g (Just (P.Rewrite (P.Defn rr') fl cl,sgs')))
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
       let ctx' = context <> Context (reverse xs) lcls
       pure $ PT opts xs lcls t (Just (r,map (deshadow ctx') sgs))

    applyRule :: [T.Name] -> T.Term -> P.Prop -> UnifyM (T.Subst, [ProofTree])
    applyRule skolems g (P.Forall (m :ms) sgs g') = do
       n <- fresh
       let mt = foldl T.Ap n (map T.LocalVar [0..length skolems - 1])
       applyRule skolems g (P.subst mt 0 (P.Forall ms sgs g'))
    applyRule skolems g (P.Forall [] sgs g') = do
       (,map fromProp sgs) <$> unifier g g'

deshadow :: Context -> ProofTree -> ProofTree
deshadow ctx (PT disp names locals term mc) = let 
      names' = map (disambiguate (bound ctx)) names
      ctx' = ctx <> Context (reverse names') locals
    in PT disp names' locals term (fmap (fmap (map (deshadow ctx'))) mc)
  where 
    disambiguate :: [T.Name] -> T.Name -> T.Name
    disambiguate ns n | n `notElem` ns = n
                      | otherwise = disambiguate ns (nextName n)

    nextName n | numbers <- MS.takeWhileEnd isDigit n, not (MS.null numbers), prefix <- MS.dropWhileEnd isDigit n
               = prefix <> MS.pack (show $ (read (MS.unpack numbers) :: Int) + 1)
    nextName n = n <> "\'"


normaliseEquality :: Path -> ProofTree -> ProofTree
normaliseEquality p = over (path p) (reapplyContext (snd . unflatten . fmap removeRefls . flip flatten p . convertRewriteToTrans))

unflatten :: (T.Term, [(T.Term, ProofTree, Path)]) -> (T.Term, ProofTree )
unflatten (t, []) = error "Shouldn't happen"
unflatten (t, (t', pt, _) : []  ) = (t', pt)
unflatten (t, (t', pt, _) : rest) = 
  let  (rhs, pt') = unflatten (t', rest)
  in  (rhs, PT Nothing [] [] (T.Ap (T.Ap (T.Const "_=_" False) t) rhs) (Just (P.Transitivity,[pt,pt'])))

reapplyContext :: (ProofTree -> ProofTree) -> ProofTree -> ProofTree
reapplyContext f pt@(PT opts names locals _ _) = let (PT _ _ _ goal rest) = f pt 
                                                  in PT opts names locals goal rest

flatten :: ProofTree -> Path -> (T.Term, [(T.Term, ProofTree, Path)])
flatten a@(PT _ _ _ (T.Ap (T.Ap (T.Const "_=_" False) g1) g2) (Just (P.Transitivity,[sg1,sg2]))) pth = (g, as ++ bs)
  where (g,as) = flatten sg1 (0:pth)
        (g',bs) = flatten sg2 (1:pth)
flatten a@(PT _ _ _ (T.Ap (T.Ap (T.Const "_=_" False) g1) g2) (Just (P.Rewrite rn fl (Just P.LHS),
            (a'@(PT _ _ _ (T.Ap (T.Ap (T.Const "_=_" False) g1') g2') mpt) : rest)))) pth = (g1, (g1',a,pth):as) 
  where (_,as) = flatten a' (0:pth)
flatten a@(PT _ _ _ (T.Ap (T.Ap (T.Const "_=_" False) g1) g2) (Just (P.Rewrite rn fl (Just P.RHS),
            (a'@(PT _ _ _ (T.Ap (T.Ap (T.Const "_=_" False) g1') g2') mpt) : rest)))) pth = (g1, as ++ [(g2,flipDir a,pth)]) 
  where (_,as) = flatten a' (0:pth)
        flipDir (PT opts ctx lcls goal (Just (P.Rewrite rn fl l, sgs))) = (PT opts ctx lcls goal (Just (P.Rewrite rn (not fl) l, sgs)))
        flipDir xs = xs
flatten pt@(PT _ _ _ (T.Ap (T.Ap (T.Const "_=_" False) g1) g2) _) pth = (g1, [(g2, pt,pth)])
flatten (PT opts sks lcls g mgs) pth = (g, [])

removeRefls :: [(T.Term, ProofTree, Path)] -> [(T.Term, ProofTree, Path)]
removeRefls xs = case filter notRefl xs of [] -> xs; xs' -> xs'
  where 
    notRefl (_,PT _ _ _ (T.Ap (T.Ap (T.Const "_=_" False) g1) g2) (Just (P.Refl,[])),_) = False 
    notRefl _ = True

applyRewrite :: P.NamedProp -> Bool -> Path -> ProofTree -> UnifyM ProofTree
applyRewrite (r,prp) shouldReverse p pt = do
    do (pt', subst) <- runWriterT $ iatraverseOf (path p) pure guts pt
       pure $ applySubst subst pt'
  where
    guts :: Context -> ProofTree -> WriterT T.Subst UnifyM ProofTree
    guts context (PT d xs lcls t _) = do
       (subst, r, sgs) <- lift $ applyEq (reverse xs ++ bound context) shouldReverse t (r,prp)
       tell subst
       let ctx' = context <> Context (reverse xs) lcls
       pure $ PT d xs lcls t (Just (r, map (deshadow ctx') sgs))

applyEq :: [T.Name] -> Bool -> T.Term -> P.NamedProp -> UnifyM (T.Subst, P.RuleRef, [ProofTree])
applyEq skolems shouldReverse g (r,(P.Forall (m :ms) sgs g')) = do
  n <- fresh
  let mt = foldl T.Ap n (map T.LocalVar [0..length skolems -1])
  applyEq skolems shouldReverse g (r,(P.subst mt 0 (P.Forall ms sgs g')))
applyEq skolems shouldReverse g (r,(P.Forall [] sgs g')) = do
  (s,t,cp) <- match skolems g sgs g'
  return (s,P.Rewrite r shouldReverse cp,((PT Nothing [] [] t Nothing):(map fromProp sgs)))
  where
    match :: [T.Name] -> T.Term -> [P.Prop] -> T.Term -> UnifyM (T.Subst, T.Term, Maybe P.CalcLocation)
    match skolems  g sgs g' = (do
      a <- fresh
      let ma = foldl T.Ap a (map T.LocalVar [0..length skolems -1])
      s <- if shouldReverse then unifier g' (T.Ap (T.Ap (T.Const "_=_" False) ma) g) else unifier g' (T.Ap (T.Ap (T.Const "_=_" False) g) ma)
      return (s, ma, Nothing)) <|> case g of
        (T.Lam (T.M x) e) -> do
          (a,b,_) <- match (x:skolems) e sgs (T.raise 1 g')
          return (a, T.Lam (T.M x) b, Nothing)
        (T.Ap (T.Ap op e1) e2) -> (do
          (a,b,_) <- match skolems op sgs g'
          return (a, T.Ap (T.Ap b e1) e2, Nothing)) <|> (do
            (a,b,_) <- match skolems e1 sgs g'
            return (a, T.Ap (T.Ap op b) e2, Just P.LHS)) <|> (do 
              (a,b,_) <- match skolems e2 sgs g'
              return (a, T.Ap (T.Ap op e1) b, Just P.RHS))
        (T.Ap e1 e2) -> (do
          (a,b,_) <- match skolems e1 sgs g'
          return (a, T.Ap b e2, Nothing)) <|> do
            (a,b,_) <- match skolems e2 sgs g'
            return (a, (T.Ap e1 b), Nothing)
        otherwise -> empty

-- Wrapper for elim rules
-- Params: Rule to apply, path to apply it to, which assumption to apply elim to
applyElim :: P.NamedProp -> Path -> P.NamedProp -> ProofTree -> UnifyM ProofTree 
applyElim (r,prp) p (rr,assm) pt = do
    do (pt', subst) <- runWriterT $ iatraverseOf (path p) pure guts pt
       pure $ applySubst subst pt'
  where
    guts :: Context -> ProofTree -> WriterT T.Subst UnifyM ProofTree
    guts context (PT opts xs lcls t _) = do
       (subst, sgs) <- lift $ applyRuleElim (reverse xs ++ bound context) t prp
       tell subst
       let ctx' = context <> Context (reverse xs) lcls
       pure $ PT opts xs lcls t (Just (P.Elim r rr,map (deshadow ctx') sgs))

    -- Identical to applyRule (for Intro) above but also tries to unify with an assumption
    -- Will only try to unify goal if it unifies with an assumption
    applyRuleElim :: [T.Name] -> T.Term -> P.Prop -> UnifyM (T.Subst, [ProofTree])
    applyRuleElim skolems g r@(P.Forall ms (P.Forall [] [] t:sgs) g') = do 
        let indices = T.mentioned t
        (result,x) <- foldM (\(r,count) i -> (,) <$> instantiate skolems (i-count) r <*> pure (count+1) ) (r,0) (sort indices)
        let (P.Forall ms' (s:sgs') g') = result
        substs <- P.unifierProp (P.raise (length ms') assm) s
        let introRule = P.applySubst substs (P.Forall ms' sgs' g')
        (substs', sgs'') <- applyRule skolems g introRule 
        pure (substs <> substs', sgs'')
    applyRuleElim skolems g _ = empty
    
    applyRule :: [T.Name] -> T.Term -> P.Prop -> UnifyM (T.Subst, [ProofTree])
    applyRule skolems g (P.Forall (m:ms) sgs g')
      | (T.LocalVar k,args) <- T.peelApTelescope g', k == length ms = do
         let cutoff = length (m:ms) 
         let exclusions = map (subtract cutoff) $ filter (>= cutoff) $ concatMap T.mentioned args 
         n <- fresh
         let mt = foldl T.Ap n (map T.LocalVar $ filter (`notElem` exclusions) $ [0..length skolems - 1]) 
         applyRule skolems g (P.subst mt 0 (P.Forall ms sgs g')) 
      | otherwise = do
         n <- fresh
         let mt = foldl T.Ap n (map T.LocalVar [0..length skolems - 1])
         applyRule skolems g (P.subst mt 0 (P.Forall ms sgs g'))
    applyRule skolems g r@(P.Forall [] sgs g') = do
       (,map fromProp sgs) <$> unifier g g'

-- Instantiate the variable at index i with a fresh unification variable
instantiate :: [T.Name] -> T.Index -> P.Prop -> UnifyM P.Prop
instantiate skolems i r@(P.Forall [] sgs g) = do 
    pure (P.Forall [] sgs g)
instantiate skolems i r@(P.Forall ms sgs g) = do 
    let (outer,_:inner) = splitAt (length ms - i - 1) ms
    n <- fresh  -- [CPM] Returns increasing #, always unique
    let mt = foldl T.Ap n (map T.LocalVar [(0 + length outer)..(length skolems - 1 + length outer)])
    let skolems'@(P.Forall inner' sgs' g') = (P.subst mt 0 (P.Forall inner sgs g))
    pure (P.Forall (outer++inner') sgs' g')  

applySubst :: T.Subst -> ProofTree -> ProofTree
applySubst subst (PT opts sks lcls g sgs) =
    PT opts sks (map (P.applySubst subst) lcls) (T.applySubst subst g) (fmap (fmap (map (applySubst subst))) sgs)

convertRewriteToTrans :: ProofTree -> ProofTree 
convertRewriteToTrans (PT opts sks lcls (T.Ap (T.Ap (T.Const "_=_" False) a) b) 
      (Just (P.Rewrite r f (Just P.LHS), (sg@(PT _ [] [] (T.Ap (T.Ap (T.Const "_=_" False) a') b') msgs):sgs)))) 
  = PT opts sks lcls (T.Ap (T.Ap (T.Const "_=_" False) a) b) 
     (Just (P.Transitivity, [ PT Nothing [] [] (T.Ap (T.Ap (T.Const "_=_" False) a) a') 
                                (Just (P.Rewrite r f (Just P.LHS), PT Nothing [] [] (T.Ap (T.Ap (T.Const "_=_" False) a') a') (Just (P.Refl, [])):sgs))
                            , convertRewriteToTrans sg]))
convertRewriteToTrans (PT opts sks lcls (T.Ap (T.Ap (T.Const "_=_" False) a) b) 
      (Just (P.Rewrite r f (Just P.RHS), (sg@(PT _ [] [] (T.Ap (T.Ap (T.Const "_=_" False) a') b') msgs):sgs)))) 
  = PT opts sks lcls  (T.Ap (T.Ap (T.Const "_=_" False) a) b) 
     (Just (P.Transitivity, [convertRewriteToTrans sg, PT Nothing [] [] (T.Ap (T.Ap (T.Const "_=_" False) b') b) 
                                   (Just (P.Rewrite r (not f) (Just P.LHS), PT Nothing [] [] (T.Ap (T.Ap (T.Const "_=_" False) b) b) (Just (P.Refl, [])):sgs))]))  
convertRewriteToTrans (PT opts sks lcls g (Just (P.Transitivity, [ sg1, sg2 ]))) = 
     PT opts sks lcls g (Just (P.Transitivity, [ convertRewriteToTrans sg1, convertRewriteToTrans sg2 ]))
convertRewriteToTrans pt = pt 

nix :: ProofTree -> ProofTree 
nix (PT opts sks lcls (T.Ap (T.Ap (T.Const "_=_" False) a) b) 
      (Just (P.Rewrite r f (Just P.LHS), (sg@(PT _ [] [] (T.Ap (T.Ap (T.Const "_=_" False) a') b') msgs):_)))) 
  = PT opts sks lcls  (T.Ap (T.Ap (T.Const "_=_" False) a) b) (Just (P.Transitivity, [PT Nothing [] [] (T.Ap (T.Ap (T.Const "_=_" False) a) a') Nothing, sg]))
nix (PT opts sks lcls (T.Ap (T.Ap (T.Const "_=_" False) a) b) 
      (Just (P.Rewrite r f (Just P.RHS), (sg@(PT _ [] [] (T.Ap (T.Ap (T.Const "_=_" False) a') b') msgs):_)))) 
  = PT opts sks lcls  (T.Ap (T.Ap (T.Const "_=_" False) a) b) (Just (P.Transitivity, [sg, PT Nothing [] [] (T.Ap (T.Ap (T.Const "_=_" False) b') b) Nothing]))  
nix (PT opts sks lcls g _) = PT opts sks lcls g Nothing

clear :: P.RuleName -> ProofTree -> ProofTree
clear toClear x@(PT opts sks lcl g (Just (rr,sgs)))
     | matches rr = PT opts sks lcl g Nothing
     | otherwise  = PT opts sks lcl g $ Just (rr, map (clear toClear) sgs)
  where 
    matches :: P.RuleRef -> Bool 
    matches (P.Elim t t') = any matches [t, t']  
    matches (P.Rewrite t _ _) = matches t
    matches (P.Defn t) = t == toClear
    matches r = P.defnName r == Just toClear
clear toClear x = x

renameRule :: (P.RuleName, P.RuleName) -> ProofTree -> ProofTree
renameRule (s,s') pt = over dependencies subst pt
  where
    subst n = if n == s then s' else n

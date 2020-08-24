{-# LANGUAGE FlexibleContexts #-}
module Unification
   where
import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Logic
import           Control.Monad.Trans
import Control.Monad.Except
import qualified Data.Map.Strict     as M
import           Data.Maybe
import           Data.Foldable
import qualified Data.Set            as S
import Debug.Trace
--------------------------------------------------
------------------ the language ------------------
--------------------------------------------------

type Id = String 
newtype Masked a = M a 
instance Eq (Masked a) where 
   _ == _ = True 
instance Show a => Show (Masked a) where
  show (M a) = show a
instance Ord (Masked a) where
  compare _ _ = EQ

type Index = Int
data Term = FreeVar Id
          | LocalVar Index
          | MetaVar Id
          | Ap Term Term
          | Const String
          | Lam (Masked Id) Term
          deriving (Show, Eq, Ord)

  
-- | Raise @LocalVar@s without a binding by @i@ amount. Used to avoid
-- capture in terms with free de Bruijn variables.
raise :: Int -> Term -> Term
raise = raise' 0
raise' lower i t = case t of
   FreeVar i -> FreeVar i
   LocalVar j -> if j >= lower then LocalVar (i + j) else LocalVar j
   MetaVar i -> MetaVar i
   Const s -> Const s
   Ap l r -> raise' lower i l `Ap` raise' lower i r
   Lam n body -> Lam n (raise' (lower + 1) i body)

-- | Substitute a term for the de Bruijn variable @i@.
subst :: Term -> Int -> Term -> Term
subst new i t = case t of
  FreeVar i -> FreeVar i
  LocalVar j -> case compare j i of
    LT -> LocalVar j
    EQ -> new
    GT -> LocalVar (j - 1)
  MetaVar i -> MetaVar i
  Ap l r -> subst new i l `Ap` subst new i r
  Const s -> Const s
  Lam n body -> Lam n (subst (raise 1 new) (i + 1) body)

-- | Substitute a term for all metavariables with a given identifier.
substMV :: Term -> Id -> Term -> Term
substMV new i t = case t of
  FreeVar i -> FreeVar i
  LocalVar i -> LocalVar i
  MetaVar j -> if i == j then new else MetaVar j
  Ap l r -> substMV new i l `Ap` substMV new i r
  Const s -> Const s
  Lam n body -> Lam n (substMV (raise 1 new) i body)

-- | Substitute a term for all free variable with a given identifier.
substFV :: Term -> Id -> Term -> Term
substFV new i t = case t of
  FreeVar j -> if i == j then new else FreeVar j
  MetaVar i -> MetaVar i
  LocalVar i -> LocalVar i
  Ap l r -> substFV new i l `Ap` substFV new i r
  Const s -> Const s
  Lam n body -> Lam n (substFV (raise 1 new) i body)

-- | Gather all the metavariables in a term into a set.
metavars :: Term -> S.Set Id
metavars t = case t of
  FreeVar i -> S.empty
  LocalVar i -> S.empty
  MetaVar j -> S.singleton j
  Ap l r -> metavars l <> metavars r
  Const s -> S.empty
  Lam n body -> metavars body

-- | Returns @True@ if a term has no free variables and is therefore a
-- valid candidate for a solution to a metavariable.
isClosed :: Term -> Bool
isClosed t = case t of
  FreeVar i -> False
  LocalVar i -> True
  MetaVar j -> True
  Const j -> True
  Ap l r -> isClosed l && isClosed r
  Lam n body -> isClosed body

-- | Implement reduction for the language. Given a term, normalize it.
-- This boils down mainly to applying lambdas to their arguments and all
-- the appropriate congruence rules.
reduce :: Term -> Term
reduce t = case t of
  FreeVar i -> FreeVar i
  LocalVar j -> LocalVar j
  MetaVar i -> MetaVar i
  Const i -> Const i
  Ap l r -> case reduce l of
    Lam n body -> reduce (subst r 0 body)
    l' -> Ap l' (reduce r)
  Lam n body -> Lam n (reduce body)

-- | Check to see if a term is blocked on applying a metavariable.
isStuck :: Term -> Bool
isStuck MetaVar {} = True
isStuck (Ap f _) = isStuck f
isStuck _ = False

-- | Turn @f a1 a2 a3 a4 ... an@ to @(f, [a1...an])@.
peelApTelescope :: Term -> (Term, [Term])
peelApTelescope t = go t []
  where go (Ap f r) rest = go f (r : rest)
        go t rest = (t, rest)

-- | Turn @(f, [a1...an])@ into @f a1 a2 a3 a4 ... an@.
applyApTelescope :: Term -> [Term] -> Term
applyApTelescope = foldl' Ap

-----------------------------------------------------------------
-------------- the actual unification code ----------------------
-----------------------------------------------------------------
type Gen a = State Int a
type UnifyM = LogicT (State Int)
type Constraint = (Term, Term)

gen :: Gen Int 
gen = do x <- get; put (x + 1); pure x


-- | Given a constraint, produce a collection of equivalent but
-- simpler constraints. Any solution for the returned set of
-- constraints should be a solution for the original constraint.
simplify :: Constraint -> UnifyM (S.Set Constraint)
simplify (t1, t2)
  | t1 == t2 && S.null (metavars t1) = return S.empty
  | reduce t1 /= t1 = simplify (reduce t1, t2)
  | reduce t2 /= t2 = simplify (t1, reduce t2)
  | (FreeVar i, cxt) <- peelApTelescope t1,
    (FreeVar j, cxt') <- peelApTelescope t2 = do
      guard (i == j && length cxt == length cxt')
      fold <$> mapM simplify (zip cxt cxt')
  | (Const i, cxt) <- peelApTelescope t1,
    (Const j, cxt') <- peelApTelescope t2 = do
      guard (i == j && length cxt == length cxt')
      fold <$> mapM simplify (zip cxt cxt')
  | Lam n body1 <- t1,
    Lam n body2 <- t2 = do
      v <- FreeVar . show <$> lift gen
      return $ S.singleton (subst v 0 body1, subst v 0 body2)
  | otherwise =
    if isStuck t1 || isStuck t2 then return $ S.singleton (t1, t2) else mzero

type Subst = M.Map Id Term

-- | Generate all possible solutions to flex-rigid equations as an
-- infinite list of computations producing finite lists.
tryFlexRigid :: Constraint -> [UnifyM [Subst]]
tryFlexRigid (t1, t2)
  | (MetaVar i, cxt1) <- peelApTelescope t1,
    (stuckTerm, cxt2) <- peelApTelescope t2,
    not (i `S.member` metavars t2) = proj (length cxt1) i stuckTerm 0
  | (MetaVar i, cxt1) <- peelApTelescope t2,
    (stuckTerm, cxt2) <- peelApTelescope t1,
    not (i `S.member` metavars t1) = proj (length cxt1) i stuckTerm 0
  | otherwise = []
  where proj bvars mv f nargs =
          generateSubst bvars mv f nargs : proj bvars mv f (nargs + 1)
        generateSubst bvars mv f nargs = do
          let mkLam tm = foldr ($) tm (replicate bvars (Lam (M "x")) )
          let saturateMV tm = foldl' Ap tm (map LocalVar [0..bvars - 1])
          let mkSubst = M.singleton mv
          args <- map saturateMV . map MetaVar <$> replicateM nargs (show <$> lift gen)
          return [mkSubst . mkLam $ applyApTelescope t args
                 | t <- map LocalVar [0..bvars - 1] ++
                        if isClosed f then [f] else []]

-- | The reflexive transitive closure of @simplify@
repeatedlySimplify :: S.Set Constraint -> UnifyM (S.Set Constraint)
repeatedlySimplify cs = do
  cs' <- fold <$> traverse simplify (S.toList cs)
  if cs' == cs then return cs else repeatedlySimplify cs'

manySubst :: Subst -> Term -> Term
manySubst s t = M.foldrWithKey (\mv sol t -> substMV sol mv t) t s

(<+>) :: Subst -> Subst -> Subst
s1 <+> s2 | not (M.null (M.intersection s1 s2)) = error "Impossible"
s1 <+> s2 = M.union (manySubst s1 <$> s2) s1

(<++>) :: Subst -> Subst -> Subst
s1 <++> s2 | not (M.null (M.intersection s1 s2)) = error "Impossible"
s1 <++> s2 = M.union (manySubst s1 <$> s2) (manySubst s2 <$> s1)

-- | The top level function, given a substitution and a set of
-- constraints, produce a solution substution and the resulting set of
-- flex-flex equations.
unify :: Subst -> S.Set Constraint -> UnifyM (Subst, S.Set Constraint)
unify s cs | traceShow cs True = do
  let cs' = applySubst s cs
  cs'' <- repeatedlySimplify cs'
  let (flexflexes, flexrigids) = S.partition flexflex cs''
  if S.null flexrigids
    then return (s, flexflexes)
    else do
      let psubsts = tryFlexRigid (S.findMax flexrigids)
      trySubsts psubsts (flexrigids <> flexflexes)
  where applySubst s = S.map (\(t1, t2) -> (manySubst s t1, manySubst s t2))
        flexflex (t1, t2) = isStuck t1 && isStuck t2
        trySubsts [] cs = mzero
        trySubsts (mss : psubsts) cs = do
          ss <- mss
          traceShowM ss 
          let these = foldr interleave mzero [unify (newS <+> s) cs | newS <- ss]
          let those = trySubsts psubsts cs
          these `interleave` those

runUnifyM :: UnifyM a -> Gen [a]
runUnifyM = observeManyT 1

{-
-- V = MetaVar
-- C = Const/FreeVar
-- B = LocalVar
-- $ = Ap
-- A = Lam

-- newV = gen
-- strip = peelApTelescope
-- abs = lam
-}

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

-- zip?

proj sS s = case peelApTelescope (devar sS s) of
        (Lam _ t,_) -> proj sS t
        (Const _,ss) -> foldlM proj sS ss
        (FreeVar _,ss) -> foldlM proj sS ss
        (LocalVar i,ss) | i >= 0 -> foldlM proj sS ss
                        | otherwise -> throwError "Unification Failure i < 0"
        (MetaVar f,bs) -> do
           var <- MetaVar . show <$> lift gen
           bs' <- posM ( \ t -> case t of (LocalVar i) -> pure (i >= 0)
                                          otherthing  -> throwError ("Non-pattern equation") ) bs
           pure ((f , hnf bs var bs' ):sS)


flexflex1 f ym zn sS 
    | ym == zn =  pure $ sS 
    | otherwise = do
       var <- MetaVar . show <$> lift gen
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
         h <- MetaVar . show <$> lift gen
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
  | otherwise = throwError "Unification Error (rigid, rigid)"




-- | Solve a constraint and return the remaining flex-flex constraints
-- and the substitution for it.
unifier :: Term-> Term -> S.Set Constraint -> Gen (Maybe (Subst, S.Set Constraint))
unifier t1 t2 flexes = do
  x <- runExceptT $ unif [] (t1,t2)
  case x of Left _ -> pure Nothing
            Right s -> pure (Just ( foldr (<++>) M.empty (map (uncurry M.singleton) s), S.fromList []))
-- fmap listToMaybe $ runUnifyM $ unify M.empty $ S.union (S.singleton (t1,t2)) flexes


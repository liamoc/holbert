{-# LANGUAGE TupleSections, FlexibleContexts, GADTs, DeriveAnyClass, DeriveGeneric, OverloadedStrings #-}
module Prop where
import Unification
import qualified StringRep as SR
import Miso.String(MisoString)
import qualified Miso.String as MS
import qualified Terms as T
import GHC.Generics(Generic)
import Data.Aeson (ToJSON,FromJSON)
import Data.Maybe (fromJust,mapMaybe)
import Optics.Indexed.Core
import Optics.IxAffineTraversal
import Optics.Lens
import Optics.Iso
import Optics.Core
import Control.Applicative
import Data.List(foldl',elemIndex)

type RuleName = MisoString

data RuleRef = Defn RuleName
             | Local Int
             | Cases MisoString Int
             | Induction MisoString Int
             -- below are for presentation only in proofs
             | Refl -- built in equality law
             | Rewrite RuleRef Bool -- bool is if it is flipped
             | Elim RuleRef RuleRef
             deriving (Eq, Show, Generic, ToJSON, FromJSON)

defnName :: RuleRef -> Maybe RuleName
defnName v = case v of
  Defn n -> Just n
  Cases s i -> Just $ "§cases-" <> s <> "§" <> MS.pack (show i)
  Induction s i -> Just $ "§induction-" <> s <> "§" <> MS.pack (show i)
  _ -> Nothing

builtInRefl :: NamedProp
builtInRefl = (Refl, Forall ["x"] [] (T.applyApTelescope (T.Const "_=_") [T.LocalVar 0, T.LocalVar 0]))

type NamedProp = (RuleRef, Prop)
data Prop = Forall [T.Name] [Prop] T.Term deriving (Eq, Ord, Show, Generic, ToJSON, FromJSON)

type Path = [Int]

type RuleContext = [T.Name]

infixl 9 %.
(%.) a b = icompose (flip (++)) (a % b)

premise :: Int -> IxAffineTraversal' RuleContext Prop Prop
premise n = premises % ix n

path :: [Int] -> IxAffineTraversal' RuleContext Prop Prop
path [] = iatraversal (Right . ([],)) (const id)
path (x:xs) = path xs %. premise x

premises :: IxLens' RuleContext Prop [Prop]
premises = ilens (\(Forall xs lcls _) -> (reverse xs, lcls))
                 (\(Forall xs _    t) lcls -> Forall xs lcls t)

conclusion :: IxLens' RuleContext Prop T.Term
conclusion = ilens (\(Forall xs _    t) -> (reverse xs, t))
                   (\(Forall xs lcls _) t -> Forall xs lcls t)

metabinders :: Lens' Prop [T.Name]
metabinders = lens (\(Forall xs _    _) -> xs)
                   (\(Forall _  lcls t) xs -> Forall xs lcls t)

blank :: Prop
blank = Forall [] [] (T.Const "???")

removePremise :: Int -> Prop -> Prop
removePremise i (Forall vs lcls g) = let (first,_:rest) = splitAt i lcls
                                      in Forall vs (first ++ rest) g

addBinders :: [T.Name] -> Prop -> Prop
addBinders news prop = foldl' (flip addBinder) prop news
addBinder :: T.Name -> Prop -> Prop
addBinder new (Forall vs lcls g) =  Forall (vs ++ [new]) (map (raise 1) lcls) (T.raise 1 g)

isBinderUsed :: Int -> Prop -> Bool
isBinderUsed x (Forall vs lcls g) = let
     dbi = length vs - x - 1
     used = T.isUsed dbi g || any (isUsed dbi) lcls
  in used

removeBinder :: Int -> Prop -> Prop
removeBinder x (Forall vs lcls g) = let
    dbi = length vs - x - 1
    (first,_:last) = splitAt x vs
    g' = T.subst (T.Const "???") dbi g
    lcls' = map (subst (T.Const "???") dbi) lcls
 in Forall (first ++ last) lcls' g'

isUsed :: Int -> Prop -> Bool
isUsed x (Forall vs lcls g) = T.isUsed (x + length vs) g || any (isUsed (x + length vs)) lcls

raise :: Int -> Prop -> Prop
raise = raise' 0

raise' :: Int -> Int -> Prop -> Prop
raise' l n (Forall xs ps g) = Forall xs (map (raise' (l + length xs) n) ps) (T.raise' (l + length xs) n g )

subst :: T.Term -> Int -> Prop -> Prop
subst t n (Forall xs rls g) = let
     t' = T.raise (length xs) t
     n' = n + length xs
     rls' = map (subst t' n') rls
     g' = T.subst t' n' g
  in Forall xs rls' g'

-- we do no raising because substitutions should only map metavariables to closed terms
applySubst :: T.Subst -> Prop -> Prop
applySubst subst (Forall vs lcls g) = Forall vs (map (applySubst subst) lcls) (T.applySubst subst g)

-- A bit disappointing that this can't be cleanly lensified.
getConclusionString :: SR.SyntaxTable -> Path -> Prop -> MisoString
getConclusionString tbl p prp = let (ctx, trm) = fromJust (ipreview (path p %. conclusion) prp)
                             in SR.prettyPrint tbl ctx trm

setConclusionString :: SR.SyntaxTable -> Path -> MisoString -> Prop -> Either MisoString Prop
setConclusionString tbl p txt prp = iatraverseOf (path p %. conclusion) Right parse prp
  where
    parse ctx _ = SR.parse tbl ctx txt

inductionRule :: MisoString -> Int -> [(MisoString, Int)] -> [Prop] -> NamedProp
inductionRule str i formers cases = 
  let subgoals = map caseSubgoal cases
      names' = map (\i -> "§" <> MS.pack (show i)) (take i [0..])
      Just ii = elemIndex (str,i) formers
      elimAsm = T.applyApTelescope (T.Const str) (map T.LocalVar $ reverse [0..i-1])
      conclusion = T.applyApTelescope (T.LocalVar $ i + ii) (map T.LocalVar $ reverse [0..i-1])
      names'' = map (\i -> "§P" <> MS.pack (show i)) (take (length formers) [0..])
      in (Induction str i, Forall (names'' ++ names') (Forall [] [] elimAsm:subgoals) conclusion)
  where
    caseSubgoal (Forall vs sgs t) 
      | (T.Const k, rest) <- T.peelApTelescope t , Just ii <- elemIndex (k,length rest) formers
         = let newConc = T.applyApTelescope (T.LocalVar (length vs + i + ii)) rest
               sgs' = mapMaybe (eachSubgoal (length vs)) sgs
               eachSubgoal offset (Forall vvs sggs tt) 
                 | (T.Const kk, sgRest) <- T.peelApTelescope tt
                 , Just iii <- elemIndex (kk, length sgRest) formers
                 = let sggs' = mapMaybe (eachSubgoal $ offset + length vvs) sggs 
                    in Just (Forall vvs (sggs' ++ sggs) $ T.applyApTelescope (T.LocalVar (length vvs + offset + i + iii)) sgRest)
               eachSubgoal _ _ = Nothing
            in (Forall vs (sgs' ++ sgs) newConc)
      | otherwise = error "Not valid introduction rule"
caseRule :: MisoString -> Int -> [Prop] -> NamedProp
caseRule str i cases = 
  let (names, subgoals) = foldr (\c (names,r) -> let (names', r') = caseSubgoal c in (merge names names', r':r))
                                (replicate i Nothing,[]) cases 
      names' = zipWith (\i mn -> maybe ("§" <> MS.pack (show i)) id mn) [0..] names
      elimAsm = T.applyApTelescope (T.Const str) (map T.LocalVar $ reverse [0..i-1])
      in (Cases str i, Forall ("§P":names') (Forall [] [] elimAsm:subgoals) (T.LocalVar i))
  where
    merge = zipWith (<|>)
    caseSubgoal (Forall vs sgs t) 
      | (T.Const k, rest) <- T.peelApTelescope t , length rest == i, k == str
         = let (sgs', vs', rest',names) = formatArgs vs rest sgs (i-1)
            in (names, Forall vs' sgs' (T.LocalVar (length vs' + i)))
      | otherwise = error "Not valid introduction rule"
  
    formatArgs vs [] sgs i = (sgs,vs,[],[])
    formatArgs vs (a:as) sgs i
      = case a of 
          T.LocalVar n | n < length vs 
            -> let (lefts,name:rights) = splitAt (length vs - n-1) vs
                   vs' = lefts ++ rights
                   a' = T.LocalVar (i + length vs')
                   (sgs', vs'', as',names) = formatArgs vs' (map (T.subst a' n) as) (map (subst a' n) sgs) (i-1)
                in (sgs', vs'', T.LocalVar (i + length vs''):as', Just name:names)
          _ -> let (sgs',  vs', as',names) = formatArgs vs as sgs (i-1)
                   sg = Forall [] [] $ T.Ap (T.Ap (T.Const "_=_") (T.LocalVar (i + length vs'))) a
                in (sg:sgs', vs', T.LocalVar (i + length vs'): as', Nothing:names)

isRewrite :: Prop -> Bool 
isRewrite (Forall _ _ c) | (T.Const "_=_", rest) <- T.peelApTelescope c = True
isRewrite _ = False

isIntroduction :: Prop -> Bool 
isIntroduction (Forall _ _ c) | (T.Const _, rest) <- T.peelApTelescope c = True
isIntroduction _ = False

introRoot :: Prop -> (MisoString, Int)
introRoot (Forall _ _ c) | (T.Const k, rest) <- T.peelApTelescope c = (k, length rest)
introRoot _ = error "Not an intro rule!"

unifierProp :: Prop -> Prop -> UnifyM T.Subst
unifierProp (Forall [] [] p1) (Forall [] [] p2) = unifier p1 p2
unifierProp _ _ = empty

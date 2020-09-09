{-# LANGUAGE TupleSections, FlexibleContexts, GADTs, DeriveAnyClass, DeriveGeneric #-}
module Prop where
import Unification
import StringRep
import qualified Terms as T
import GHC.Generics(Generic)
import Data.Aeson (ToJSON,FromJSON)
import Data.Maybe (fromJust)
import Optics.Indexed.Core
import Optics.IxAffineTraversal
import Optics.Lens
import Optics.Iso
import Optics.Core

type RuleName = String

data RuleRef = Defn RuleName
             | Local Int
             deriving (Eq, Show, Generic, ToJSON, FromJSON)

type NamedProp = (RuleRef, Prop)
data Prop = Forall [String] [Prop] T.Term deriving (Eq, Ord, Show, Generic, ToJSON, FromJSON)

type Path = [Int]

type RuleContext = [T.Id]

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

metabinders :: Lens' Prop [T.Id]
metabinders = lens (\(Forall xs _    _) -> xs)
                   (\(Forall _  lcls t) xs -> Forall xs lcls t)

blank :: Prop
blank = Forall [] [] (T.Const "???")

removePremise :: Int -> Prop -> Prop
removePremise i (Forall vs lcls g) = let (first,_:rest) = splitAt i lcls
                                      in Forall vs (first ++ rest) g

addBinder :: T.Id -> Prop -> Prop
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
getConclusionString :: Path -> Prop -> String
getConclusionString p prp = let (ctx, trm) = fromJust (ipreview (path p %. conclusion) prp)
                             in toSexps ctx trm

setConclusionString :: Path -> String -> Prop -> Either String Prop
setConclusionString p txt prp = iatraverseOf (path p %. conclusion) Right parse prp
  where
    parse ctx _ = fromSexps ctx txt


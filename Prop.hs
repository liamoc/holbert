module Prop where 
import Control.Monad
import Unification
import Terms
import Data.Maybe
import Data.List
import Debug.Trace
import StringRep

data Prop = Forall [String] ([Prop]) Term deriving (Eq, Ord, Show)

data RuleRef = Defn String | Local Int deriving (Eq, Show)

type Path = [Int]

modifyAtE :: Int -> (a -> Either e a) -> [a] -> Either e [a]
modifyAtE i f xs 
  = let (lefts, r:rights) = splitAt i xs
     in (lefts ++) . (:rights) <$> f r

modifyAt' :: Int -> (a -> (a, b)) -> [a] -> ([a], b)
modifyAt' i f xs 
  = let (lefts, r:rights) = splitAt i xs
        (r',b) = f r
     in (lefts ++ r':rights, b)

modifyAtMany :: Int -> (a -> [a]) -> [a] -> [a]
modifyAtMany i f xs 
  = let (lefts, r:rights) = splitAt i xs
     in lefts ++ (f r ++ rights)
modifyAt :: Int -> (a -> a) -> [a] -> [a]
modifyAt i f xs 
  = let (lefts, r:rights) = splitAt i xs
     in lefts ++ (f r:rights)

subRule' :: Path -> (Prop -> (Prop,a)) -> Prop -> (Prop, a)
subRule' [] f = f 
subRule' (p:ps) f = subRule' ps (\(Forall sks lcls g) ->  let (lcls', b) = modifyAt' p f lcls in (Forall sks lcls' g, b))

subRule :: Path -> (Prop -> Prop) -> Prop -> Prop
subRule [] f = f 
subRule (p:ps) f = subRule ps (\(Forall sks lcls g) -> Forall sks (modifyAt p f lcls) g)

subRuleCtx :: Path -> ([String] -> Prop -> Either String Prop) -> Prop -> Either String Prop
subRuleCtx [] f = f []
subRuleCtx (p:ps) f = subRuleCtx ps (\ctx (Forall sks lcls g) -> flip (Forall sks) g <$> modifyAtE p (f (reverse sks ++ ctx)) lcls)


ruleString :: Path -> Prop -> String
ruleString p prp = case subRuleCtx p (\ctx (Forall vs _ g) -> Left (toSexps (reverse vs ++ ctx) g)) prp of 
                     Left e -> e
                     _ -> error "Impossible"

addBlankPremise :: Prop -> (Prop,Int)
addBlankPremise (Forall vs lcls g) = (Forall vs (lcls ++ [Forall [] [] (Const "???")]) g, length lcls)

removePremise :: Int -> Prop -> Prop
removePremise i (Forall vs lcls g) = let (first,_:rest) = splitAt i lcls
                                      in Forall vs (first ++ rest) g

raiseProp l n (Forall xs ps g) = Forall xs (map (raiseProp (l + length xs) n) ps) (raise' (l + length xs) n g )
 

substProp :: Term -> Int -> Prop -> Prop 
substProp t n (Forall [] rls g) = Forall [] (map (substProp t n) rls) (subst t n g)
substProp t n (Forall (x :xs) rls g) = 
  let (Forall xs' rls' g') = substProp (raise 1 t) (n + 1) (Forall xs rls g)
   in Forall (x :xs') rls' g'


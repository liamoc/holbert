module Prop where 
import Control.Monad
import Unification as U
import Data.Maybe
import Data.List
import Debug.Trace
import StringRep
import qualified Data.Set as S
type Base a = U.Gen a

data Prop = Forall [String] ([Prop]) U.Term deriving (Eq, Ord, Show)

data RuleRef = Defn String | Local Int deriving (Eq, Show)
data ProofTree = Goal ([String]) ([Prop]) U.Term 
               | Rule RuleRef ([String]) ([Prop]) U.Term ([ProofTree]) deriving (Eq, Show)

data ProofTreeContext = PTC  RuleRef ([String]) ([Prop]) U.Term ([ProofTree]) ([ProofTree]) deriving (Eq, Show)

data Zipper = Zip Path ([ProofTreeContext]) ProofTree deriving (Eq, Show)

type Path = [Int]





allSkolems :: ProofTree -> [String]
allSkolems (Goal sks _ _) = sks
allSkolems (Rule _ sks _ _ pts) = sks ++ concatMap allSkolems pts

up :: Zipper -> Maybe Zipper 
up (Zip pth ctx (Rule r skms lrs g (sg: sgs))) = Just (Zip (0:pth) (PTC r skms lrs g [] sgs:ctx) sg)
up _ = Nothing

down :: Zipper -> Maybe Zipper 
down (Zip (_ :pth) ((PTC r skms lrs g lefts rights): ctx) sg) = Just (Zip pth ctx (Rule r skms lrs g (lefts ++ sg:rights)))
down _ = Nothing

left :: Zipper -> Maybe Zipper
left (Zip pth ((PTC r skms lrs g (lg: lefts) rights): ctx) sg) = Just (Zip pth (PTC r skms lrs g lefts (sg:rights): ctx) lg)
left _ = Nothing

right :: Zipper -> Maybe Zipper
right (Zip pth (PTC r skms lrs g lefts (rg: rights): ctx) sg) = Just (Zip pth ((PTC r skms lrs g (sg:lefts) rights): ctx) rg)
right _ = Nothing

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

substRRPT :: String -> String -> ProofTree -> ProofTree
substRRPT new old (Rule rr sks lcls trm pts) = Rule (if rr == Defn old then Defn new else rr) sks lcls trm (map (substRRPT new old) pts)
substRRPT new old r = r 

renameMeta :: (Path, Int) -> String -> ProofTree -> ProofTree
renameMeta (p,x) s pt = do
   let z = path' p (Zip [] [] pt) 
       z' = renameMetaZ x s z
    in unwind z'

renameMetaZ :: Int -> String -> Zipper -> Zipper
renameMetaZ x s (Zip pth ctx g) = Zip pth ctx $ case g of
         (Rule rr sks lcls trm pts) ->
           let -- old = sks !! x
               sks' = modifyAt x (\_ -> s) sks
            in  Rule rr sks' lcls trm pts
         -- Rule rr sks' (map (substFVP (U.FreeVar s) old) lcls) (U.substFV (U.FreeVar s) old trm) (map (substFVPT (U.FreeVar s) old) pts)
         (Goal sks lcls trm) ->
           let -- old = sks !! x
               sks' = modifyAt x (\_ -> s) sks
            in Goal sks' lcls trm
          --Goal sks' (map (substFVP (U.FreeVar s) old) lcls) (U.substFV (U.FreeVar s) old trm)
  where
    substFVPT for i (Rule rr sks lcls trm pts) = Rule rr sks (map (substFVP for i) lcls) (U.substFV for i trm) (map (substFVPT for i) pts)
    substFVPT for i (Goal sks lcls trm) = Goal sks (map (substFVP for i) lcls) (U.substFV for i trm)

    substFVP for i (Forall vs lcls g) = Forall vs (map (substFVP for i) lcls) (U.substFV for i g)

upRightN :: Int -> Zipper -> Maybe Zipper 
upRightN 0 = up
upRightN n = right <=< upRightN (n-1)

path :: Path -> Zipper -> Maybe Zipper 
path = foldr (\n f -> upRightN n <=< f) Just

validPath :: Path -> ProofTree -> Bool
validPath p pt = not $ isNothing $ path p $ Zip [] [] pt
path' :: Path -> Zipper -> Zipper 
path' p z = fromMaybe z (path p z)
rewind :: Zipper -> Zipper 
rewind z = maybe z rewind (down z)
unwind :: Zipper -> ProofTree 
unwind z = let Zip _ _ pt = rewind z in pt 
nixFrom :: Path -> ProofTree -> ProofTree
nixFrom p pt = let (Zip pth ctx (Rule rr sks lcls g sgs)) = path' p (Zip [] [] pt)
               in unwind (Zip pth ctx (Goal sks lcls g))

doRule :: (RuleRef, Prop) -> S.Set U.Constraint -> Path -> ProofTree -> Base (Maybe (ProofTree, S.Set U.Constraint))
doRule r flexes p pt = do
   let z = path' p (Zip [] [] pt) 
   mb <- rule r flexes z
   pure $ fmap (\(z,fxs) -> (unwind z, fxs)) $ mb

queryAtPath :: Path -> (Zipper -> a) -> ProofTree -> a
queryAtPath p f pt = f (path' p (Zip [] [] pt))

getRule :: RuleRef -> [Prop] -> Maybe Prop
getRule (Local i) props = Just $ props !! i
getRule (Defn n) _ = case n of 
    "ImpI" -> Just $ Forall ["A" , "B" ]
                     [ Forall [] [Forall [] [] (U.LocalVar 1)] (U.LocalVar 0)  ]
                     (U.Ap (U.Ap (U.Const "_->_") (U.LocalVar 1)) (U.LocalVar 0))
    "ConjI" -> Just $ Forall ["A","B"]
                      [ Forall [] [] (U.LocalVar 1) 
                      , Forall [] [] (U.LocalVar 0)]
                      (U.Ap (U.Ap (U.Const "_/\\_") (U.LocalVar 1)) (U.LocalVar 0))
    "ConjE1" -> Just $ Forall ["A","B"]
                      [ Forall [] [] (U.Ap (U.Ap (U.Const "_/\\_") (U.LocalVar 1)) (U.LocalVar 0))]
                      (U.LocalVar 1)
    "ConjE2" -> Just $ Forall ["A","B"]
                      [ Forall [] [] (U.Ap (U.Ap (U.Const "_/\\_") (U.LocalVar 1)) (U.LocalVar 0))]
                      (U.LocalVar 0)
    _ -> Nothing


substMVZ :: U.Subst -> Zipper -> Zipper 
substMVZ sbst (Zip pth ctx pt) = (Zip pth (map (substMVC sbst) ctx) (substMVPT sbst pt))
  where 
    substMVC subst (PTC rr sks lcls g ls rs) =
       (PTC rr sks (map (substMVP subst) lcls) (substG subst g) (map (substMVPT subst) ls) (map (substMVPT subst) rs)) 
    substMVP subst (Forall vs lcls g) = Forall vs (map (substMVP subst) lcls) (substG subst g)
    substG subst g = U.reduce (U.manySubst subst g)
    substMVPT subst (Rule rr sks lcls g sgs) = 
        (Rule rr sks (map (substMVP subst) lcls) (substG subst g) (map (substMVPT subst) sgs))
    substMVPT subst (Goal sks lcls g) = 
        (Goal sks (map (substMVP subst) lcls) (substG subst g))

addBlankPremise :: Prop -> (Prop,Int)
addBlankPremise (Forall vs lcls g) = (Forall vs (lcls ++ [Forall [] [] (U.Const "???")]) g, length lcls)

removePremise :: Int -> Prop -> Prop
removePremise i (Forall vs lcls g) = let (first,_:rest) = splitAt i lcls
                                      in Forall vs (first ++ rest) g

rule :: (RuleRef, Prop) -> S.Set U.Constraint -> Zipper -> Base (Maybe (Zipper, S.Set U.Constraint))
rule (r,rl) flexes z@(Zip pth ctx (Goal sks lcls g)) = do
        ms <- applyRule flexes (knownSkolems z) g rl 
        case ms of 
            Nothing -> pure Nothing 
            Just (sbst, sgs, flexes') -> do 
               pure (Just (substMVZ sbst (Zip pth ctx (Rule r sks lcls g sgs)), flexes'))
rule r _ _ = pure Nothing 

knownLocals :: Zipper -> [Prop]
knownLocals (Zip _ ctx (Goal sks lcls _))= map (raiseProp 0 (length sks)) (contextLocals ctx) ++ lcls
--concatMap (\(PTC _ _ lcls _ _ _) -> lcls) ctx ++ lcls
knownLocals (Zip _ ctx (Rule _ sks lcls _ _)) = map (raiseProp 0 (length sks)) (contextLocals ctx) ++ lcls
-- knownLocals (Zip _ ctx (Rule _ _ lcls _ _)) = concatMap (\(PTC _ _ lcls _ _ _) -> lcls) ctx ++ lcls

contextLocals :: [ProofTreeContext] -> [Prop]
contextLocals [] = []
contextLocals (c@(PTC _ sks lcls _ _ _):rest) = let acc = contextLocals rest
                                                 in map (raiseProp 0 (length sks)) acc ++ lcls
raiseProp l n (Forall xs ps g) = Forall xs (map (raiseProp (l + length xs) n) ps) (raise' (l + length xs) n g )
 

knownSkolems :: Zipper -> [String]
knownSkolems (Zip _ ctx (Goal sks _ _)) = reverse sks ++ concatMap (\(PTC _ sks _ _ _ _) -> reverse sks) ctx 
knownSkolems (Zip _ ctx (Rule _ sks _ _ _)) = reverse sks ++ concatMap (\(PTC _ sks _ _ _ _) -> reverse sks) ctx


substProp :: U.Term -> Int -> Prop -> Prop 
substProp t n (Forall [] rls g) = Forall [] (map (substProp t n) rls) (U.subst t n g)
substProp t n (Forall (x :xs) rls g) = 
  let (Forall xs' rls' g') = substProp (U.raise 1 t) (n + 1) (Forall xs rls g)
   in Forall (x :xs') rls' g'

goal :: [String] -> Prop -> Base ProofTree
goal skolems (Forall [] rls g) = do 
   pure (Goal (reverse skolems) rls g)
goal skolems (Forall (x: xs) rls g) = do 
    -- x' <- enfreshinate2 x x 
    goal (x : skolems) (Forall xs rls g) -- (substProp (U.FreeVar x') 0 (Forall xs rls g)) 

applyRule :: S.Set U.Constraint -> [String] -> U.Term -> Prop -> Base (Maybe (U.Subst, [ProofTree], S.Set U.Constraint))
applyRule flexes skolems g (Forall (m :ms) sgs g') = do 
   n <- U.MetaVar . show <$> U.gen 
   let mt = foldl U.Ap n (map U.LocalVar [0..length skolems -1]) -- (map U.FreeVar skolems)
   applyRule flexes skolems g (substProp mt 0 (Forall ms sgs g'))
applyRule flexes skolems g (Forall [] sgs g') 
   = do msubst <- U.unifier g g' flexes
        sgs' <- traverse (goal []) sgs
        pure $ case msubst of 
          Just (subst,flexes') -> Just (subst, sgs', flexes')
          Nothing -> Nothing
  
enfreshinate2 :: String -> String -> Base String 
enfreshinate2 s1 s2 | s1 == s2 = do 
  x <- gen 
  pure (s1 ++ show x)
enfreshinate2 s1 s2 = do x <- gen
                         pure (s1 ++ s2 ++ show x)

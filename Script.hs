{-# LANGUAGE RankNTypes, GADTs #-}
module Script where
import Prop as P
import ProofTree
import Unification 
import Terms
import qualified Miso.String as MS
import Data.Maybe
import Control.Monad.State
import Data.Char(isSpace)
import StringRep
import Optics.Core

import Debug.Trace

type Counter = Int
data ProofState = PS ProofTree Counter deriving (Show, Eq)

proofTree :: Lens' ProofState ProofTree
proofTree = lensVL $ \act (PS pt c) -> flip PS c <$> act pt



data Item = Proposition
            { itemName :: RuleName
            , itemProp :: Prop 
            , itemPS   :: Maybe ProofState
            } 
          | Heading Int MS.MisoString
          | Block MS.MisoString
          deriving (Show, Eq)

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
type Script = [Item]

after :: Int -> AffineTraversal' [a] (a,[a])
after n = atraversalVL guts
  where
    guts :: AffineTraversalVL' [a] (a,[a])
    guts pure' act ls = let 
         (lefts,itrights) = splitAt n ls
      in case itrights of 
           (it:rights) -> 
              (\(it',rights') -> lefts ++ it':rights') <$> act (it,rights)
           _ -> pure' ls

before :: Int -> AffineTraversal' [a] ([a],a)
before n = atraversalVL guts
  where
    guts :: AffineTraversalVL' [a] ([a],a)
    guts pure' act ls = let 
         (lefts,itrights) = splitAt n ls
      in case itrights of 
           (it:rights) -> 
              (\(lefts',it') -> lefts' ++ it':rights) <$> act (lefts,it)
           _ -> pure' ls

-- Warning, don't use this if it would affect proofs afterwards, use setPropositions for that.
proposition :: AffineTraversal' Item Prop
proposition = rule % _2

reference :: AffineTraversal' Item RuleName
reference = rule % _1


proofState :: AffineTraversal' Item ProofState
proofState = atraversal
  (\i   -> case i of Proposition _ _ (Just s) -> Right s
                     i -> Left i)
  (\i s -> case i of Proposition n p (Just _) -> Proposition n p (Just s)
                     i -> i)

rule :: AffineTraversal' Item (RuleName, Prop)
rule = atraversal
  (\i        -> case i of Proposition n p s -> Right (n, p)
                          i -> Left i)
  (\i (n, p) -> case i of Proposition _ _ s -> Proposition n p s
                          i -> i)

setPropositions :: Setter' (Item,[Item]) Prop
setPropositions = sets guts
  where
    guts act (Proposition n p s, rest) 
      | p' <- act p
      = ( Proposition n p' (fmap (const $ genProofState p') s)
        , map (clearRuleItem n) rest)

definedRules :: Traversal' ([Item],Item) (RuleName, Prop)
definedRules = _1 % traversed % rule

outstandingGoals = not . null . outstandingGoals'

outstandingGoals' :: ProofState -> [ProofTree.Path]
outstandingGoals' (PS t _) = outstandingGoalsAcc [] t
  where
   outstandingGoalsAcc pth (PT _ _ _ Nothing) = [pth]
   outstandingGoalsAcc pth (PT _ _ _ (Just (_,pts))) = concat $ zipWith outstandingGoalsAcc (map (:pth) [0..]) pts 

genProofState :: Prop -> ProofState
genProofState prop = PS (fromProp prop) 0

ruleAction :: (Prop -> Prop) -> Int -> Script -> Script
ruleAction a i = modifyAt i (\(Proposition n p prf) -> Proposition n (a p) prf)

proofAction :: (ProofState -> ProofState) -> Int -> Script -> Script
proofAction a i = modifyAt i (\(Proposition n p (Just ps)) -> Proposition n p (Just $ a ps))

proofActionE :: (ProofState -> Either String ProofState) -> Int -> Script -> Either String Script
proofActionE a i = modifyAtE i (\(Proposition n p (Just ps)) -> Proposition n p . Just <$> a ps)

itemRules (Proposition n p _) = [(Defn n, p)] 
itemRules _ = []

nix :: ProofTree.Path -> ProofState -> ProofState
nix p = set (proofTree % ProofTree.path p % step) Nothing

groupedRules :: Script -> [(String, [(RuleRef, Prop)])] -> [(String, [(RuleRef, Prop)])]
groupedRules [] acc = acc 
groupedRules (Heading n str:xs) acc 
             | n < 2 = groupedRules xs ((MS.unpack $ str, []):acc)
             | otherwise = groupedRules xs acc 
groupedRules (i:xs) (h:acc) = let rs = itemRules i 
                              in groupedRules xs (fmap (rs ++) h:acc)
groupedRules (i:xs) [] = error "Script didn't start with a heading"
                 

-- todo lens
rules' :: (Int, ProofTree.Path) -> Script -> ([String], [(String, [(RuleRef, Prop)])])
rules' (i,p) s = let (lefts, Proposition n prp (Just (PS pt c)): rights) = splitAt i s
                     context = fst $ fromJust $ ipreview (ProofTree.path p %+ step) pt
                     lcls = zip (map Local [0..]) (ProofTree.locals context)
                     ctx = ProofTree.bound context
                     rules = groupedRules lefts []
                  in traceShow context (ctx, filter (not . null . snd) (("Local Facts", lcls):rules))

rules :: (Int, ProofTree.Path) -> Script -> [(RuleRef, Prop)] 
rules (i,p) s = let (lefts, Proposition n prp (Just (PS pt c)): rights) = splitAt i s
                    context = fst $ fromJust $ ipreview (ProofTree.path p %+ step) pt
                    lcls = zip (map Local [0..]) (ProofTree.locals context)
                    rules = concatMap itemRules lefts 
                 in lcls ++ rules

insertProposition :: String -> Int -> Bool -> Script -> Either String Script
insertProposition "" _ _ _ = Left "Cannot add: Name cannot be empty"
insertProposition new i isT s
   = let names = map fst $ concatMap itemRules s
         (first, last) = splitAt i s
      in if Defn new `elem` names then Left $ "Cannot add: Name '" ++ new ++ "' is used already."
         else Right $ first ++ Proposition new p mpt:last
  where
    mpt = if isT then Just (genProofState p) else Nothing
    p = Forall [] [] (Const "???")


validSelection :: (Int, ProofTree.Path) -> Script -> Bool
validSelection (i,p) s = isJust $ preview (ix i % proofState % proofTree % ProofTree.path p) s 

renameRule :: String -> Int -> Script -> Either String Script
renameRule "" i _ = Left "Cannot rename: Name cannot be empty"
renameRule new i s
   = let names = map fst $ concatMap itemRules s
         (first, Proposition n p mpt:last) = splitAt i s
      in if Defn new `elem` names then Left $ "Cannot rename: Name '" ++ new ++ "' is used already."
         else Right $ first ++ Proposition new p mpt 
                    : over (traversed % proofState % proofTree % ruleReferences) (subst n) last
  where subst old x = if x == Defn old then Defn new else x

addPremise :: Int -> P.Path -> Script -> (Script, P.Path)
addPremise i p s = let 
  s' = over (after i % setPropositions % P.path p % P.premises) (++ [P.blank]) s
  p' = length (fromJust $ preview (ix i % proposition % P.path p % P.premises) s') - 1 : p
  in (s',p')


deletePremise :: Int -> P.Path -> Script -> Script
deletePremise i (x:p) = over (after i % setPropositions % P.path p) (P.removePremise x) 

renameRuleMeta :: String -> (Int, P.Path, Int) -> Script -> Either String Script
renameRuleMeta new (i,p,x) | Just msg <- invalidName new = \_ -> Left ("Cannot rename: " ++ msg)
renameRuleMeta new (i,p,x) = Right . set (ix i % proposition % P.path p % P.metabinders % ix x) new

addRuleMeta :: String -> (Int, P.Path) -> Script -> Either String Script
addRuleMeta new (i,p) | Just msg <- invalidName new = \_ -> Left msg
addRuleMeta new (i,p) = Right . over (after i % setPropositions % P.path p) (addBinder new)

deleteRuleMeta :: (Int, P.Path, Int) -> Script -> Either String Script
deleteRuleMeta (i,p,x) s | Just True <- preview (ix i % proposition % P.path p % to (not . isBinderUsed x) ) s  
                         = Right $ over (after i % setPropositions % P.path p) (removeBinder x) s
                         | otherwise = Left "Cannot remove binder: Variable is in use"


{-
let f = modifyRule' i $ subRule' p $ \(Forall vs lcls g) -> 
                                 let dbi = length vs - x - 1
                                     used = isUsed dbi g || any (isUsedP dbi) lcls
                                     (first,_:last) = splitAt x vs
                                    g' = subst (Const "???") dbi g
                                     lcls' = map (substProp (Const "???") dbi) lcls 
                                  in (Forall (first ++ last) lcls' g', not used)
                               (s',flag) = f s
                          in if flag then Right s' else Left "Cannot remove variable: variable is in use."

-}

modifyRule :: Int -> (Prop -> Prop) -> Script -> Script
modifyRule i a s = fst $ modifyRule' i (\p -> (a p, ())) s

modifyRuleE :: Int -> (Prop -> Either e Prop ) -> Script -> Either e Script
modifyRuleE i f s 
  = let (lefts, (Proposition n p mpt):rights) = splitAt i s
        ep' = f p 
        rights' = map (clearRuleItem n) rights
     in fmap (\p' -> let 
           mpt' = fmap (\_-> genProofState p') mpt
        in lefts ++ (Proposition n p' mpt'):rights') ep'

moveItemDown :: Int -> Script -> Script
moveItemDown i s = let (lefts,x:y:rest) = splitAt i s
                       y' = case x of 
                              Proposition n _ _ -> clearRuleItem n y
                              _ -> y
                    in lefts ++ y':x:rest


clearRuleItem toClear (Proposition n p (Just (PS pt c))) = Proposition n p (Just (PS (clearRule toClear pt) c))
  where
    clearRule toClear x@(PT sks lcl g (Just (rr,sgs))) | rr == (Defn toClear) = PT sks lcl g Nothing
                                                       | otherwise            = PT sks lcl g $ Just (rr, map (clearRule toClear) sgs)
    clearRule toClear x = x
clearRuleItem toClear p = p

deleteItem :: Int -> Script -> Script
deleteItem i s
  = let (lefts, it:rights) = splitAt i s
        rights' = case it of (Proposition n _ _) -> map (clearRuleItem n) rights
                             _ -> rights
     in lefts ++ rights'

modifyRule' :: Int -> (Prop -> (Prop,a)) -> Script -> (Script, a)
modifyRule' i f s 
  = let (lefts, (Proposition n p mpt):rights) = splitAt i s
        (p',a) = f p 
        mpt' = fmap (\_-> genProofState p') mpt
        rights' = map (clearRuleItem n) rights
     in (lefts ++ (Proposition n p' mpt'):rights', a)

invalidName "" = Just "Name cannot be empty"
invalidName s | any isSpace s = Just "Name contains spaces"
invalidName s | any (`elem` ("()." :: String)) s = Just "Name contains reserved symbols"
invalidName s = Nothing

renameProofMeta :: String -> (Int, ProofTree.Path, Int) -> Script -> Either String Script
renameProofMeta new (i,p,x) | Just msg <- invalidName new = \_ -> Left ("Cannot rename: " ++ msg)
renameProofMeta new (i,p,x) = Right . set (ix i % proofState % proofTree % ProofTree.path p % goalbinders % ix x) new

apply :: RuleRef -> (Int, ProofTree.Path) -> Script -> Either String Script
apply rr (i,p) s = let rls = rules (i,p) s
                       onPS (PS pt c) = case lookup rr rls of 
                                          Nothing -> Left "Rule not found"
                                          Just prp -> case runUnifyM (ProofTree.apply (rr,prp) p pt) c of
                                             (Left e,_) -> Left $ "Cannot apply rule: " ++ e  
                                             (Right pt',c') -> Right (PS pt' c')
                    in proofActionE onPS i s

updateRuleTerm :: String -> (Int, P.Path) -> Script -> Either String Script
updateRuleTerm str (i, p) s = over (after i % setPropositions) id
                          <$> atraverseOf (ix i % proposition) Right (setConclusionString p str) s
       {-      error "TODO" modifyRuleE i $ subRuleCtx p $ \ctx (Forall vs lcls g) -> 
               case (fromSexps (reverse vs ++ ctx) str) of 
setConclusionString :: Path -> String -> Prop -> Either String Prop
                 Left e -> Left e
setConclusionString :: Path -> String -> Prop -> Either String Prop
setConclusionString p txt prp = toIxAtraversalVL (path p % conclusion) Right parse prp
  where 
    parse ctx _ = fromSexp ctx txt

                 Right g' -> Right (Forall vs lcls g') -}

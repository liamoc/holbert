module Script where
import Prop
import ProofTree
import Unification 
import Terms
import qualified Miso.String as MS
import Data.Maybe
import Control.Monad.State
import Data.Char(isSpace)
import StringRep

data ProofState = PS { stateTree :: ProofTree, counter :: Int} deriving (Show, Eq)

data Item = Proposition
            { itemName :: String
            , itemProp :: Prop 
            , itemPS   :: Maybe ProofState
            } 
          | Heading Int MS.MisoString
          | Block MS.MisoString
          deriving (Show, Eq)

type Script = [Item]



outstandingGoals = not . null . outstandingGoals'

outstandingGoals' :: ProofState -> [Path]
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

nix :: Path -> ProofState -> ProofState
nix p i = i { stateTree = nixFrom p (stateTree i) }


groupedRules :: Script -> [(String, [(RuleRef, Prop)])] -> [(String, [(RuleRef, Prop)])]
groupedRules [] acc = acc 
groupedRules (Heading n str:xs) acc 
             | n < 2 = groupedRules xs ((MS.unpack $ str, []):acc)
             | otherwise = groupedRules xs acc 
groupedRules (i:xs) (h:acc) = let rs = itemRules i 
                              in groupedRules xs (fmap (rs ++) h:acc)
groupedRules (i:xs) [] = error "Script didn't start with a heading"
                 


rules' :: (Int, Path) -> Script -> ([String], [(String, [(RuleRef, Prop)])])
rules' (i,p) s = let (lefts, Proposition n prp (Just (PS pt c)): rights) = splitAt i s
                     lcls = zip (map Local [0..]) (queryAtPath p knownLocals pt)
                     ctx = queryAtPath p knownSkolems pt
                     rules = groupedRules lefts []
                  in (ctx, filter (not . null . snd) (("Local Facts", lcls):rules))

rules :: (Int, Path) -> Script -> [(RuleRef, Prop)] 
rules (i,p) s = let (lefts, Proposition n prp (Just (PS pt c)): rights) = splitAt i s
                    lcls = zip (map Local [0..]) (queryAtPath p knownLocals pt)
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

renameRule :: String -> Int -> Script -> Either String Script
renameRule "" i _ = Left "Cannot rename: Name cannot be empty"
renameRule new i s
   = let names = map fst $ concatMap itemRules s
         (first, Proposition n p mpt:last) = splitAt i s
      in if Defn new `elem` names then Left $ "Cannot rename: Name '" ++ new ++ "' is used already."
         else Right $ first ++ Proposition new p mpt:map (substRRItem new n) last
  where substRRItem new n (Proposition nm p (Just (PS pt c))) = Proposition nm p (Just (PS (substRRPT new n pt) c))
        substRRItem new n p = p
validSelection :: (Int, Path) -> Script -> Bool
validSelection (i,p) s = validPath p $ stateTree $ fromJust $ itemPS $ s !! i


addPremise :: Int -> Path -> Script -> (Script, Path)
addPremise i p s = (:p) <$> modifyRule' i (subRule' p addBlankPremise) s

deletePremise :: Int -> Path -> Script -> Script
deletePremise  i (x:p) = modifyRule i (subRule p  $ removePremise x)

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

updateRuleTerm :: String -> (Int, Path) -> Script -> Either String Script
updateRuleTerm str (i, p) 
  = modifyRuleE i $ subRuleCtx p $ \ctx (Forall vs lcls g) -> 
               case (fromSexps (reverse vs ++ ctx) str) of 
                 Left e -> Left e
                 Right g' -> Right (Forall vs lcls g')

addRuleMeta :: String -> (Int, Path, Int) -> Script -> Either String Script
addRuleMeta new (i,p,x) | Just msg <- invalidName new = \_ -> Left msg
addRuleMeta new (i,p,x) = fmap Right $ modifyRule i $ subRule p $ \(Forall vs lcls g) -> Forall (vs ++ [new]) (map (raiseP 0) lcls) (raise 1 g) 
     where
       raiseP lower (Forall vs lcls g) = Forall vs (map (raiseP (lower + length vs)) lcls) (raise' (lower + length vs) 1 g)

deleteRuleMeta :: (Int, Path, Int) -> Script -> Either String Script
deleteRuleMeta (i,p,x) s = let f = modifyRule' i $ subRule' p $ \(Forall vs lcls g) -> 
                                 let dbi = length vs - x - 1
                                     used = isUsed dbi g || any (isUsedP dbi) lcls
                                     (first,_:last) = splitAt x vs
                                     g' = subst (Const "???") dbi g
                                     lcls' = map (substProp (Const "???") dbi) lcls 
                                  in (Forall (first ++ last) lcls' g', not used)
                               (s',flag) = f s
                          in if flag then Right s' else Left "Cannot remove variable: variable is in use."
       where isUsedP x (Forall vs lcls g) = isUsed (x + length vs) g || any (isUsedP (x + length vs)) lcls


renameRuleMeta :: String -> (Int, Path, Int) -> Script -> Either String Script
renameRuleMeta new (i,p,x) | Just msg <- invalidName new = \_ -> Left ("Cannot rename: " ++ msg)
renameRuleMeta new (i,p,x) = Right . flip ruleAction i (subRule p $ \(Forall sks lcl g) -> Forall (modifyAt x (\_ -> new) sks) lcl g)

renameProofMeta :: String -> (Int, Path, Int) -> Script -> Either String Script
renameProofMeta new (i,p,x) | Just msg <- invalidName new = \_ -> Left ("Cannot rename: " ++ msg)
renameProofMeta new (i,p,x) 
   = flip proofActionE i $ \(PS pt c) ->
       Right $ PS (renameMeta (p,x) new pt) c 

apply :: RuleRef -> (Int, Path) -> Script -> Either String Script
apply rr (i,p) s = let rls = rules (i,p) s
                       onPS (PS pt c) = case lookup rr rls of 
                                          Nothing -> Left "Rule not found"
                                          Just prp -> case runState (doRule (rr,prp) p pt) c of
                                             (Nothing,_) -> Left "Cannot apply rule (no unifier)"
                                             (Just (pt'),c') -> Right (PS pt' c')
                    in proofActionE onPS i s


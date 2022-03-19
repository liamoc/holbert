{-# LANGUAGE TypeFamilies, DeriveAnyClass, DeriveGeneric, OverloadedStrings #-}
module Rule where
import qualified ProofTree as PT
import qualified Prop as P
import qualified Terms as T
import Controller
import Unification
import Debug.Trace
import Miso.String (MisoString, pack)
import Data.String
import qualified Miso.String as MS
import Optics.Core
import StringRep
import Control.Monad(when)
import Data.Maybe(fromMaybe,fromJust,mapMaybe)
import GHC.Generics(Generic)
import Data.Aeson (ToJSON,FromJSON)

data RuleType
  = Axiom
  | InductionInit
  | InductionPrinc
  | Theorem
  deriving (Show, Eq, Generic, ToJSON, FromJSON)

data RuleItem = RI P.RuleName P.Prop (Maybe ProofState)
  deriving (Show, Eq, Generic, ToJSON, FromJSON)
data Rule = R RuleType [RuleItem]
  deriving (Show, Eq, Generic, ToJSON, FromJSON)

type Counter = Int
data ProofState = PS PT.ProofTree Counter
  deriving (Show, Eq, Generic, ToJSON, FromJSON)

name :: Lens' RuleItem P.RuleName
name = lensVL $ \act (RI n prp m) -> (\n' -> RI n' prp m) <$> act n

blankAxiom :: RuleType -> P.RuleName -> Rule
blankAxiom ruleType n = (R ruleType [RI n P.blank Nothing])

blankTheorem :: RuleType -> P.RuleName -> Rule
blankTheorem ruleType n = (R ruleType [RI n P.blank (Just $ PS (PT.fromProp P.blank) 0)])

-- in future: genInductionPrinc
ruleItems :: IxTraversal' Int Rule RuleItem 
ruleItems = itraversalVL guts
  where 
    --guts :: forall f. Applicative f => (RuleItem -> f RuleItem) -> Rule -> f Rule 
    guts f (R t ls) =  R t <$> traverse (\(i, e) -> f i e) (zip [0..] ls)
  
-- warning, do not use this lens to assign to anything that might invalidate the proof state
-- use propUpdate for that (which will reset the proof state)
prop :: Lens' RuleItem P.Prop
prop = lensVL $ \act (RI n prp m) -> (\prp' -> RI n prp' m) <$> act prp

-- disjoint product of prop and name
namedProp :: Lens' RuleItem P.NamedProp
namedProp = lensVL $ \act (RI n prp m) -> (\(P.Defn n',prp') -> RI n' prp' m) <$> act (P.Defn n, prp)

propUpdate :: Setter' RuleItem P.Prop
propUpdate = sets guts
  where
    guts act (RI n p s)
      | p' <- act p
      = RI n p' (fmap (const $ PS (PT.fromProp p') 0) s)

proofState :: AffineTraversal' RuleItem ProofState
proofState =  atraversal
  (\i   -> case i of RI _ _ (Just s) -> Right s
                     i -> Left i)
  (\i s -> case i of RI n p (Just _) -> RI n p (Just s)
                     i -> i)


applyRewriteTactic :: RuleItem  -> P.NamedProp -> Bool -> PT.Path -> Maybe RuleAction
applyRewriteTactic state np rev pth = 
  case traverseOf proofState (runUnifyPS $ PT.applyRewrite np rev pth) state of
     Left _ -> Nothing
     Right st' -> flip Tactic pth <$> preview proofState st'
applyERuleTactic :: RuleItem -> P.NamedProp -> P.NamedProp -> PT.Path -> Maybe RuleAction
applyERuleTactic state assm np pth = 
  case traverseOf proofState (runUnifyPS $ PT.applyElim np pth assm) state of
     Left _ -> Nothing 
     Right st' -> flip Tactic pth <$> preview proofState st'


applyRuleTactic :: RuleItem -> P.NamedProp -> PT.Path -> Maybe RuleAction
applyRuleTactic state  np pth = 
  case traverseOf proofState (runUnifyPS $ PT.apply np pth) state of
     Left _ -> Nothing
     Right st' -> flip Tactic pth <$> preview proofState st'

unresolved :: ProofState -> Bool
unresolved (PS pt c) = has PT.outstandingGoals pt

proofTree :: Lens' ProofState PT.ProofTree
proofTree = lensVL $ \act (PS pt c) -> flip PS c <$> act pt

runUnifyPS :: (PT.ProofTree -> UnifyM PT.ProofTree) -> ProofState -> Either UnifyError ProofState
runUnifyPS act (PS pt c) = case runUnifyM (act pt) c of
                             (Left e, c) -> Left e
                             (Right pt',c') -> Right (PS pt' c')

checkVariableName :: MS.MisoString -> Controller f ()
checkVariableName new = case T.invalidName new of
  Just e  -> errorMessage $ "Invalid variable name: " <> pack e
  Nothing -> pure ()

data ProofFocus = GoalFocus [(P.NamedProp, RuleAction)]
                | RewriteGoalFocus Bool [(P.NamedProp, RuleAction)]
                | AssumptionFocus Int [(P.NamedProp, RuleAction)]
                | MetavariableFocus Int
                | SubtitleFocus PT.Path
                | ProofBinderFocus PT.Path Int deriving (Show, Eq)

data GoalSummary = GS [(PT.Path,Int,T.Name)] [(P.NamedProp, Maybe RuleAction)] T.Term PT.Path Bool deriving (Show, Eq)

getGoalSummary :: RuleItem -> PT.Path -> Maybe GoalSummary
getGoalSummary state' f = GS <$> pure (associate state' f)
                                 <*> fmap (map tryApply . zip (map P.Local [0 ..]) . PT.locals . fst)  (ipreview (PT.path f PT.%+ PT.step) =<< preview (proofState % proofTree) state')
                                 <*> preview (proofState % proofTree % PT.path f % PT.inference) state' 
                                 <*> pure f <*> pure False
  where 
    tryApply r = (r,  applyRuleTactic state' r f)
    associate (RI _ _ (Just (PS pt _))) f = go [] (reverse f) pt
    go pth [] pt = zipWith (\i n -> (pth, i, n)) [0..] (view PT.goalbinders pt)
    go pth (x:xs) pt = zipWith (\i n -> (pth, i, n)) [0..] (view PT.goalbinders pt) ++ case preview (PT.subgoal x) pt of 
                         Nothing -> [] 
                         Just sg -> go (x:pth) xs sg 

data RuleFocus = ProofFocus ProofFocus (Maybe GoalSummary)
                  | RuleBinderFocus P.Path Int
                  | NewRuleBinderFocus P.Path
                  | RuleTermFocus P.Path
                  | NameFocus
                  deriving (Show, Eq)

data RuleAction = Tactic ProofState PT.Path
                  | ToggleStyle PT.Path
                  | SetSubgoalHeading PT.Path
                  | Nix PT.Path
                  | SelectGoal PT.Path
                  | ExamineAssumption Int
                  | RewriteGoal Bool
                  | RenameProofBinder PT.Path Int
                  | AddRuleBinder P.Path
                  | RenameRuleBinder P.Path Int
                  | DeleteRuleBinder P.Path Int
                  | UpdateTerm P.Path
                  | AddPremise P.Path
                  | DeletePremise P.Path
                  | Rename
                  | InstantiateMetavariable Int
                  | DeleteRule Int P.RuleName
                  deriving (Show, Eq)


editableRI tbl (ProofFocus (ProofBinderFocus pth i) g) = preview (proofState % proofTree % PT.path pth % PT.goalbinders % ix i)
editableRI tbl (RuleBinderFocus pth i) = preview (prop % P.path pth % P.metabinders % ix i)
editableRI tbl (RuleTermFocus pth) = Just . P.getConclusionString tbl pth . view prop
editableRI tbl (ProofFocus (MetavariableFocus i) g) = const (Just ("?" <> pack (show i)))
editableRI tbl NameFocus = preview name
editableRI tbl (ProofFocus (SubtitleFocus pth) g) = fmap (fromMaybe "Show:" . fmap PT.subtitle) . preview (proofState % proofTree % PT.path pth % PT.style)
editableRI _ _ = const Nothing



leaveFocusRI (ProofFocus (ProofBinderFocus p i) g) = noFocus . handleRI (RenameProofBinder p i) --These define the action when the user leaves focus on an item
leaveFocusRI (RuleBinderFocus p i)  = noFocus . handleRI (RenameRuleBinder p i)
leaveFocusRI (NewRuleBinderFocus p) = noFocus . handleRI (AddRuleBinder p)
leaveFocusRI (RuleTermFocus p)      = noFocus . handleRI (UpdateTerm p)
leaveFocusRI NameFocus              = noFocus . handleRI Rename
--TODO handle other foci?
leaveFocusRI _                      = pure


handleRI :: RuleAction -> RuleItem -> Controller RuleFocus RuleItem
handleRI (SelectGoal pth) state = do
    let summary = getGoalSummary state pth 
    rules <- filter (P.isIntroduction . snd) <$> getKnownRules
    setFocus (ProofFocus (GoalFocus $ mapMaybe (\r -> (,) r <$> applyRuleTactic state r pth) rules) summary)
    pure state
handleRI (ExamineAssumption i) state = do 
  foc <- getOriginalFocus 
  case foc of 
    Just (ProofFocus _ (Just gs@(GS _ lcls _ p _))) | (it:_) <- drop i lcls -> do
      rules <- getKnownRules
      setFocus (ProofFocus (AssumptionFocus i (mapMaybe (\r -> (,) r <$> applyERuleTactic state (fst it) r p) rules)) (Just gs))
      pure state
    _ -> pure state
handleRI (RewriteGoal rev) state = do 
  foc <- getOriginalFocus 
  case foc of 
    Just (ProofFocus _ (Just gs@(GS _ _ t p _)))  -> do
      rules <- filter (P.isRewrite . snd) <$> getKnownRules
      setFocus (ProofFocus (RewriteGoalFocus rev (mapMaybe (\r -> (,) r <$> applyRewriteTactic state r rev p ) rules)) (Just gs))
      pure state
    _ -> pure state
handleRI (Tactic ps pth) state = let 
        state' = set proofState ps state 
        newFocus = if has (proofState % proofTree % PT.path (0:pth)) state'
                    then Just (0:pth)
                    else fst <$> ipreview (isingular (proofState % proofTree % PT.outstandingGoals)) state'
      in do
        case newFocus of
          Just f -> handleRI (SelectGoal f) state'
          _      -> clearFocus >> pure state'
handleRI (ToggleStyle pth) state = do
  let f Nothing = Just (PT.PDD { PT.proseStyle = True, PT.subtitle = "Show:" })
      f (Just pdd) = Just $ pdd { PT.proseStyle = not (PT.proseStyle pdd)}
  pure $ over (proofState % proofTree % PT.path pth % PT.style) f state
handleRI (SetSubgoalHeading pth) state = do
  new <- textInput
  let f Nothing = Just (PT.PDD {  PT.proseStyle = False, PT.subtitle = new })
      f (Just pdd) = Just $ pdd { PT.subtitle = new }
  foc <- getOriginalFocus
  let state' = over (proofState % proofTree % PT.path pth % PT.style) f state
  case foc of
    Just (ProofFocus _ (Just (GS _ _ _ p _))) -> handleRI (SelectGoal p) state'
    _ -> pure state'
handleRI (Nix pth) state = do
    clearFocus
    pure $ set (proofState % proofTree % PT.path pth % PT.step) Nothing state

handleRI (RenameProofBinder pth i) state = do
    new <- textInput
    checkVariableName new
    let state' = set (proofState % proofTree % PT.path pth % PT.goalbinders % ix i) new state
    foc <- getOriginalFocus
    case foc of
      Just (ProofFocus _ (Just (GS _  _ _ p _))) -> handleRI (SelectGoal p) state'
      _ -> pure state'

handleRI (AddRuleBinder pth) state = do
    new <- textInput
    checkVariableName new
    invalidate (view name state)
    setFocus (RuleTermFocus pth)
    pure $ over (propUpdate % P.path pth) (P.addBinder new) state

handleRI (RenameRuleBinder pth i) state = do
    new <- textInput
    checkVariableName new
    clearFocus -- should it be updateterm?
    pure $ set (prop % P.path pth % P.metabinders % ix i) new state

handleRI (DeleteRuleBinder pth i) state = do
    when (maybe False (P.isBinderUsed i) $ preview (prop % P.path pth) state) $ errorMessage "Cannot remove binder: is in use"
    invalidate (view name state)
    clearFocus
    pure $ over (propUpdate % P.path pth) (P.removeBinder i) state

handleRI (UpdateTerm pth) state = do
    new <- textInput
    tbl <- syntaxTable
    case toLensVL prop (P.setConclusionString tbl pth new) state of
      Left e -> errorMessage $ "Parse error: " <> e
      Right state' -> do
        invalidate (view name state')
        case pth of [] -> clearFocus
                    (_:pth') -> setFocus (RuleTermFocus pth')
        pure $ over propUpdate id state' --hack..
handleRI (InstantiateMetavariable i) state = do
  new <- textInput
  tbl <- syntaxTable
  case parse tbl [] new of
    Left e -> errorMessage $ "Parse error: " <> e
    Right obj -> do
        foc <- getOriginalFocus
        let state' = over (proofState % proofTree) (PT.applySubst (T.fromUnifier [(i,obj)])) state
        case foc of
          Just (ProofFocus _ (Just (GS _  _ _ p _))) -> handleRI (SelectGoal p) state'
          _ -> pure state'

handleRI (AddPremise pth) state = do
    invalidate (view name state)
    let newIndex = length $ fromMaybe [] (preview (prop % P.path pth % P.premises) state)
    setFocusWithLeaving (RuleTermFocus (newIndex:pth))
    pure $ over (propUpdate % P.path pth % P.premises) (++[P.blank]) state

handleRI (DeletePremise []) state = pure state -- shouldn't happen
handleRI (DeletePremise (x:pth)) state = do
    invalidate (view name state)
    setFocus (RuleTermFocus (pth))
    pure $ over (propUpdate % P.path pth) (P.removePremise x) state

handleRI Rename state = do
    new <- textInput
    when (new == "") $ errorMessage "Name cannot be empty"
    renameResource (view name state) new
    clearFocus
    pure $ set name new state

-- data Rule = R RuleType [RuleItem]
-- remove ri !! n from Rule
-- pass in list or ruleitems, select n, return state with new list of rule items?
handleRI (DeleteRule idx ruleName) state = do
  traceM ("Rule name: " ++ (fromString (MS.fromMisoString ruleName)) ++ " | Index: " ++ fromString (MS.fromMisoString (MS.toMisoString idx)))
  pure state

instance Control Rule where
  data Focus Rule = RF Int RuleFocus
                  | AddingRule
                  | Testing
                  deriving (Show, Eq)

  data Action Rule = RA Int RuleAction
                   | AddRule
                  --  | DeleteRule Int P.RuleName
                   | Test
                   deriving (Show, Eq)

  defined (R _ ls) = map (\(RI n prp _) -> (P.Defn n,prp) ) ls

  inserted _ = RF 0 (RuleTermFocus []) --When you've inserted an item switches to the relevant focus

  invalidated s r = over (ruleItems % proofState % proofTree) (PT.clear s) r --Whenever we change a rule this goes through the document and removes it from use in proofs

  renamed (s,s') r = over (ruleItems % proofState % proofTree) (PT.renameRule (s,s')) r --If we change the *name* of a rule we just update its name throughout the document

  editable tbl (RF i rf) (R _ ls) = editableRI tbl rf (ls !! i)
  editable tbl AddingRule _ = Nothing
  editable tbl Testing _ = Nothing

  leaveFocus (RF i rf) r = atraverseOf (elementOf ruleItems i) pure (leaveFocusRI rf) r
  leaveFocus AddingRule r = pure r
  leaveFocus Testing r = pure r

  handle (RA i a) r = zoomFocus (RF i) (\(RF i' rf) -> if i == i' then Just rf else Nothing) (atraverseOf (elementOf ruleItems i) pure (handleRI a) r)
  handle AddRule (R t ls) = do
    name <- textInput
    newResource name
    let s' = R t (RI name P.blank Nothing:ls) 
    setFocus (RF 0 $ RuleTermFocus [])
    pure s'

  -- data Rule = R RuleType [RuleItem]
  -- remove ri !! n from Rule
  -- pass in list or ruleitems, select n, return state with new list of rule items?
  -- handle (DeleteRule idx ruleName) r = do
  --   traceM ("Rule name: " ++ (fromString (MS.fromMisoString ruleName)) ++ " | Index: " ++ fromString (MS.fromMisoString (MS.toMisoString idx)))
  --   clearFocus
  --   pure r

  handle Test r = do
    traceM "test"
    clearFocus
    pure r
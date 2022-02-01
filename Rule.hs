{-# LANGUAGE TypeFamilies, DeriveAnyClass, DeriveGeneric, OverloadedStrings #-}
module Rule where
import qualified ProofTree as PT
import qualified Prop as P
import qualified Terms as T
import Controller
import Unification
import Miso.String (MisoString, pack)
import qualified Miso.String as MS
import Optics.Core
import StringRep
import Control.Monad(when)
import Data.Maybe(fromMaybe)
import GHC.Generics(Generic)
import Data.Aeson (ToJSON,FromJSON)

data Rule = R P.RuleName P.Prop (Maybe ProofState)
  deriving (Show, Eq, Generic, ToJSON, FromJSON)

type Counter = Int
data ProofState = PS PT.ProofTree Counter
  deriving (Show, Eq, Generic, ToJSON, FromJSON)

name :: Lens' Rule P.RuleName
name = lensVL $ \act (R n prp m) -> (\n' -> R n' prp m) <$> act n

blankAxiom :: P.RuleName -> Rule
blankAxiom n = (R n P.blank Nothing)

blankTheorem :: P.RuleName -> Rule
blankTheorem n = (R n P.blank (Just $ PS (PT.fromProp P.blank) 0))

-- warning, do not use this lens to assign to anything that might invalidate the proof state
-- use propUpdate for that (which will reset the proof state)
prop :: Lens' Rule P.Prop
prop = lensVL $ \act (R n prp m) -> (\prp' -> R n prp' m) <$> act prp

-- disjoint product of prop and name
namedProp :: Lens' Rule P.NamedProp
namedProp = lensVL $ \act (R n prp m) -> (\(P.Defn n',prp') -> R n' prp' m) <$> act (P.Defn n, prp)

propUpdate :: Setter' Rule P.Prop
propUpdate = sets guts
  where
    guts act (R n p s)
      | p' <- act p
      = R n p' (fmap (const $ PS (PT.fromProp p') 0) s)

proofState :: AffineTraversal' Rule ProofState
proofState =  atraversal
  (\i   -> case i of R _ _ (Just s) -> Right s
                     i -> Left i)
  (\i s -> case i of R n p (Just _) -> R n p (Just s)
                     i -> i)


applyRuleTactic :: Rule -> P.NamedProp -> PT.Path -> Maybe (Action Rule)
applyRuleTactic state np pth = 
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

checkVariableName :: MS.MisoString -> Controller (Focus Rule) ()
checkVariableName new = case T.invalidName new of
  Just e  -> errorMessage $ "Invalid variable name: " <> pack e
  Nothing -> pure ()

instance Control Rule where
  data Focus Rule = GoalFocus PT.Path Bool
                  | ProofBinderFocus PT.Path Int
                  | ProofSubtitleFocus PT.Path
                  | RuleBinderFocus P.Path Int
                  | NewRuleBinderFocus P.Path
                  | RuleTermFocus P.Path
                  | NameFocus
                  | MetavariableFocus Int
                  deriving (Show, Eq)

  data Action Rule = Rewrite Bool P.NamedProp PT.Path -- TODO replace with Tactic
                   | Tactic ProofState PT.Path
                   | ToggleStyle PT.Path
                   | ToggleEquational PT.Path
                   | SetSubgoalHeading PT.Path
                   | Nix PT.Path
                   | RenameProofBinder PT.Path Int
                   | AddRuleBinder P.Path
                   | RenameRuleBinder P.Path Int
                   | DeleteRuleBinder P.Path Int
                   | UpdateTerm P.Path
                   | AddPremise P.Path
                   | DeletePremise P.Path
                   | Rename
                   | InstantiateMetavariable Int
                   deriving (Show, Eq)

  defined (R n _ _) = [n] --If an item has defined some rules, they will be returned in a list

  inserted _ = RuleTermFocus [] --When you've inserted an item switches to the relevant focus

  invalidated s r = over (proofState % proofTree) (PT.clear s) r --Whenever we change a rule this goes through the document and removes it from use in proofs

  renamed (s,s') r = over (proofState % proofTree) (PT.renameRule (s,s')) r --If we change the *name* of a rule we just update its name throughout the document

  editable tbl (ProofBinderFocus pth i) = preview (proofState % proofTree % PT.path pth % PT.goalbinders % ix i)
  editable tbl (RuleBinderFocus pth i) = preview (prop % P.path pth % P.metabinders % ix i)
  editable tbl (RuleTermFocus pth) = Just . P.getConclusionString tbl pth . view prop
  editable tbl (MetavariableFocus i) = const (Just ("?" <> pack (show i)))
  editable tbl NameFocus = preview name
  editable tbl (ProofSubtitleFocus pth) = fmap (fromMaybe "Subgoal" . fmap PT.subtitle) . preview (proofState % proofTree % PT.path pth % PT.style)
  editable _ _ = const Nothing


  leaveFocus (ProofBinderFocus p i) = noFocus . handle (RenameProofBinder p i) --These define the action when the user leaves focus on an item
  leaveFocus (RuleBinderFocus p i)  = noFocus . handle (RenameRuleBinder p i)
  leaveFocus (NewRuleBinderFocus p) = noFocus . handle (AddRuleBinder p)
  leaveFocus (RuleTermFocus p)      = noFocus . handle (UpdateTerm p)
  leaveFocus NameFocus              = noFocus . handle Rename
  leaveFocus _                      = pure

  handle (Tactic ps pth) state = let 
          state' = set proofState ps state 
          newFocus = if has (proofState % proofTree % PT.path (0:pth)) state'
                     then Just (0:pth)
                     else fst <$> ipreview (isingular (proofState % proofTree % PT.outstandingGoals)) state'
        in do
          case newFocus of
            Just f -> setFocus (GoalFocus f False)
            _      -> clearFocus
          pure state'
  handle (Rewrite rev np pth) state = case traverseOf proofState (runUnifyPS $ PT.applyRewrite np rev pth) state of
     Left e -> errorMessage e >> pure state
     Right state' -> let
          newFocus = if has (proofState % proofTree % PT.path (0:pth)) state'
                     then Just (0:pth)
                     else fst <$> ipreview (isingular (proofState % proofTree % PT.outstandingGoals)) state'
        in do
          case newFocus of
            Just f -> setFocus (GoalFocus f False)
            _      -> clearFocus
          pure state'
  handle (ToggleStyle pth) state = do
    let f Nothing = Just (PT.PDD { PT.proofStyle = PT.Prose, PT.subtitle = "Subgoal" })
        f (Just pdd) = Just $ pdd { PT.proofStyle = PT.toggleStyle (PT.proofStyle pdd)}
    pure $ over (proofState % proofTree % PT.path pth % PT.style) f state
  handle (ToggleEquational pth) state = do
    let f Nothing = Just (PT.PDD { PT.proofStyle = PT.Equational, PT.subtitle = "Subgoal"})
        f (Just pdd) = case PT.proofStyle pdd of
          PT.Equational -> Just $ pdd {PT.proofStyle = PT.Tree}
          _ -> Just $ pdd {PT.proofStyle = PT.Equational}
    pure $ over (proofState % proofTree % PT.path pth % PT.style) f state
  handle (SetSubgoalHeading pth) state = do
    new <- textInput
    let f Nothing = Just (PT.PDD {  PT.proofStyle = PT.Tree, PT.subtitle = new })
        f (Just pdd) = Just $ pdd { PT.subtitle = new }
    pure $ over (proofState % proofTree % PT.path pth % PT.style) f state


  handle (Nix pth) state = do
     clearFocus
     pure $ set (proofState % proofTree % PT.path pth % PT.step) Nothing state

  handle (RenameProofBinder pth i) state = do
     new <- textInput
     checkVariableName new
     clearFocus -- should it be updateterm?
     pure $ set (proofState % proofTree % PT.path pth % PT.goalbinders % ix i) new state

  handle (AddRuleBinder pth) state = do
     new <- textInput
     checkVariableName new
     invalidate (view name state)
     setFocus (RuleTermFocus pth)
     pure $ over (propUpdate % P.path pth) (P.addBinder new) state

  handle (RenameRuleBinder pth i) state = do
     new <- textInput
     checkVariableName new
     clearFocus -- should it be updateterm?
     pure $ set (prop % P.path pth % P.metabinders % ix i) new state

  handle (DeleteRuleBinder pth i) state = do
     when (maybe False (P.isBinderUsed i) $ preview (prop % P.path pth) state) $ errorMessage "Cannot remove binder: is in use"
     invalidate (view name state)
     clearFocus
     pure $ over (propUpdate % P.path pth) (P.removeBinder i) state

  handle (UpdateTerm pth) state = do
     new <- textInput
     tbl <- syntaxTable
     case toLensVL prop (P.setConclusionString tbl pth new) state of
       Left e -> errorMessage $ "Parse error: " <> e
       Right state' -> do
         invalidate (view name state')
         case pth of [] -> clearFocus
                     (_:pth') -> setFocus (RuleTermFocus pth')
         pure $ over propUpdate id state' --hack..
  handle (InstantiateMetavariable i) state = do
    new <- textInput
    tbl <- syntaxTable
    case parse tbl [] new of
      Left e -> errorMessage $ "Parse error: " <> e
      Right obj -> do
         pure $ over (proofState % proofTree) (PT.applySubst (T.fromUnifier [(i,obj)])) state

  handle (AddPremise pth) state = do
     invalidate (view name state)
     let newIndex = length $ fromMaybe [] (preview (prop % P.path pth % P.premises) state)
     setFocusWithLeaving (RuleTermFocus (newIndex:pth))
     pure $ over (propUpdate % P.path pth % P.premises) (++[P.blank]) state

  handle (DeletePremise []) state = pure state -- shouldn't happen
  handle (DeletePremise (x:pth)) state = do
     invalidate (view name state)
     setFocus (RuleTermFocus (pth))
     pure $ over (propUpdate % P.path pth) (P.removePremise x) state

  handle Rename state = do
     new <- textInput
     when (new == "") $ errorMessage "Name cannot be empty"
     renameResource (view name state) new
     clearFocus
     pure $ set name new state

{-# LANGUAGE OverloadedStrings #-}
module View.Prop where
import Terms
import ProofTree
import Editor 
import Prop
import View.Utils
import View.Term
import Miso hiding (on)
import Data.List (intersperse, dropWhileEnd, groupBy)
import Control.Monad
import qualified Miso.String as MS
import qualified Data.Map as M
import qualified Item as I
import qualified Rule as R

data RuleDisplayOptions = RDO { termDisplayOptions :: TermDisplayOptions, showInitialMetas :: Bool, ruleStyle :: RuleStyle, showEmptyTurnstile :: Bool } 

renderProp = renderPropName Nothing
renderPropName = renderPropNameE Nothing 
renderPropNameE editable n ctx opts prp = renderP (showInitialMetas opts) (showEmptyTurnstile opts) n (ruleStyle opts) ctx [] prp
  where
    metabinders pth vs = precontext 
                       $ (concat $ zipWith (metabinder' pth) [0..] vs)
                       ++ case editable of 
                            Just (idx, selected, n) -> case selected of 
                              ItemFocus idx' (I.RuleFocus (R.NewRuleBinderFocus pth')) 
                                   | idx == idx', pth == pth' -> [metabinderEditor Nothing (ItemAction (Just idx) (I.RuleAct (R.AddRuleBinder pth))) n]
                              ItemFocus idx' (I.RuleFocus (R.RuleTermFocus pth')) | idx' == idx, pth == pth' -> 
                                           [ button "button-icon button-icon-blue button-icon-addbinder" (SetFocus (ItemFocus idx (I.RuleFocus (R.NewRuleBinderFocus pth)))) [ typicon "plus" ]
                                           , inline "metabinder" [text "."] ]
                              _ -> []
                            _ -> []
        where precontext [] = multi []
              precontext cs = inline "rule-binders" cs

    metabinder' pth i n = case editable of 
                            Just (idx, selected, n') -> case selected of
                              ItemFocus idx' (I.RuleFocus (R.RuleBinderFocus pth' i')) 
                                   | idx == idx', pth == pth', i == i' -> [metabinderEditor (Just (idx,pth,i)) (ItemAction (Just idx) $ I.RuleAct $ R.RenameRuleBinder pth i) n'] 
                              _ -> [ button_ [class_ "editable editable-math", onClick (SetFocus (ItemFocus idx (I.RuleFocus (R.RuleBinderFocus pth i)))) ] [ metabinder n ] ]
                            Nothing -> [ metabinder n ]
    metabinderEditor exists act n = multi $ form_
        [class_ "editor editor-expanding", onSubmit act]
        [ expandingTextbox "editor-textbox" UpdateInput n
        , submitButton "button-icon button-icon-blue" [typicon "tick-outline"]
        , button "button-icon button-icon-grey" Reset [typicon "times-outline"]
        , focusHack "editor-textbox"
        ] : case exists of
               Just (idx,pth,i) -> [button "button-icon button-icon-red" (ItemAction (Just idx) $ I.RuleAct $ R.DeleteRuleBinder pth i) [typicon "trash"]]
               _ -> []

    renderTerm' ctx pth trm = case editable of 
                             Just (idx,selected, s) -> case selected of 
                                ItemFocus idx' (I.RuleFocus (R.RuleTermFocus pth')) | idx == idx', pth == pth' 
                                  -> multi $ [termEditor idx ctx pth s]
                                        ++ if pth /= [] then [button "button-icon button-icon-red" (ItemAction (Just idx) $ I.RuleAct $ R.DeletePremise pth) [typicon "trash"]]
                                                        else []
                                _ -> multi [ button "editable editable-math" (SetFocus (ItemFocus idx (I.RuleFocus (R.RuleTermFocus pth)))) [renderTermCtx ctx (termDisplayOptions opts) trm]]
                             _ -> renderTermCtx ctx (termDisplayOptions opts) trm 

    termEditor i ctx pth n = form_
        [class_ "editor editor-expanding", onSubmit (ItemAction (Just i) $ I.RuleAct $ R.UpdateTerm pth)] $
        [ expandingTextbox "editor-textbox" UpdateInput n
        , submitButton "button-icon button-icon-blue" [typicon "tick-outline"]
        , button "button-icon button-icon-grey" Reset [typicon "times-outline"]
        , focusHack "editor-textbox"
        ] 

    isSelectedOrBinders pth = case editable of 
       Just (idx,selected,n) -> case selected of 
          ItemFocus idx' (I.RuleFocus (R.RuleTermFocus pth'))      | idx == idx', pth == pth' -> True
          ItemFocus idx' (I.RuleFocus (R.RuleBinderFocus pth' _))  | idx == idx', pth == pth' -> True
          ItemFocus idx' (I.RuleFocus (R.NewRuleBinderFocus pth')) | idx == idx', pth == pth' -> True
          _ -> False
       _ -> False
    isSelected pth = case editable of 
       Just (idx,selected,n) -> case selected of 
          ItemFocus idx' (I.RuleFocus (R.RuleTermFocus pth')) | idx == idx', pth == pth' -> Just idx
          _ -> Nothing
       _ -> Nothing

    renderRR' :: RuleRef -> View EditorAction
    renderRR' rr@(Local n) = renderRR rr
    renderRR' rr@(Defn n) = span_ [] $ case editable of 
                     Just (idx, selected,n) -> case selected of
                        ItemFocus idx' (I.RuleFocus R.NameFocus) | idx == idx' -> [ruleNameEditor idx n] 
                        _ -> [button "editable editable-math" (SetFocus $ ItemFocus idx $ I.RuleFocus R.NameFocus) [ renderRR rr ]]
                     Nothing -> [ renderRR rr ]

    ruleNameEditor idx n = form_
        [class_ "editor editor-expanding", onSubmit (ItemAction (Just idx) $ I.RuleAct R.Rename)] $
        [ expandingTextbox "editor-textbox" UpdateInput n
        , submitButton "button-icon button-icon-blue" [typicon "tick-outline"]
        , button "button-icon button-icon-grey" Reset [typicon "times-outline"]
        , focusHack "editor-textbox"
        ] 

    renderP showMetas showTurnstile title style ctx pth (Forall sks lcls g) = 
       let (renderer, nextStyle) = case style of 
             Bar -> (inferrule, Dots)
             BarTurnstile -> (inferrule, Turnstile)
             Turnstile -> (entailment showTurnstile', Turnstile)
             Dots -> (hypothetical showTurnstile', Turnstile)
           ctx' = reverse sks ++ ctx
           renderNext pth prp | style /= Turnstile = renderP True showTurnstile Nothing nextStyle ctx' pth prp
           renderNext pth prp@(Forall [] [] g) | not (isSelectedOrBinders pth) = renderP True showTurnstile Nothing nextStyle ctx' pth prp
           renderNext pth prp = multi (parenthesise [renderP True showTurnstile Nothing nextStyle ctx' pth prp])
           binders = if showMetas then [metabinders pth sks] else []
           premises = zipWith renderNext (map (:pth) [0..]) lcls
           (spacer,showTurnstile') = case isSelected pth of 
             Nothing  -> (text "", showTurnstile)
             Just idx -> (button "button-icon button-icon-blue button-icon-addpremise" (ItemAction (Just idx) $ I.RuleAct $ R.AddPremise pth) [typicon "plus-outline"], True)
           ruleTitle =  fmap renderRR' title
           conclusion = [renderTerm' ctx' pth g]
       in renderer binders premises spacer ruleTitle conclusion

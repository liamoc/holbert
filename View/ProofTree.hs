{-# LANGUAGE OverloadedStrings #-}
module View.ProofTree where

import Terms
import Prop
import ProofTree
import Editor 
import View.Prop
import View.Utils
import View.Term
import Miso hiding (on)
import Data.List (intersperse, dropWhileEnd, groupBy)
import qualified Miso.String as MS
import qualified Data.Map as M

import qualified Item as I
import qualified Rule as R

renderProofTree :: DisplayOptions -> Int -> ProofTree -> Maybe (R.Focus R.Rule, MS.MisoString) -> View EditorAction
renderProofTree opts idx pt selected = renderPT [] [] [] pt
  where
    termDOs = tDOs opts
    ruleDOs = RDO { termDisplayOptions = termDOs , showEmptyTurnstile = False, showInitialMetas = True, ruleStyle = Turnstile }

    renderPT :: [Prop] -> [String] -> ProofTree.Path -> ProofTree -> View EditorAction
    renderPT rns ctx pth (PT sks lcls prp msgs) = let
           binders = (if (showMetaBinders opts) then concat (zipWith (metabinder' pth) [0..] sks) else []) 
                  ++ (if (assumptionsMode opts == Hidden) then map rulebinder [length rns..length rns+length lcls - 1] else []) 
           premises = case msgs of  
                     Just (rr,sgs) -> zipWith (renderPT rns' ctx') (map (:pth) [0..]) sgs
                     Nothing       -> []
           spacer = case msgs of 
                     Just _ -> text "" 
                     _ -> goalButton pth
           ruleTitle = maybe (text "?") (addNix . renderRR . fst) msgs
           conclusionTerm = renderTermCtx ctx' termDOs prp
           conclusion = case assumptionsMode opts of 
                        New | not (null lcls) -> [numberedAssumptions [length rns..] lcls , turnstile, conclusionTerm]
                        Cumulative            -> [numberedAssumptions [0..]          rns' , turnstile, conclusionTerm]
                        _                     -> [conclusionTerm]
        in inferrule binders premises spacer ruleTitle conclusion
      where
        addNix t = multi [t, button "nix" (ItemAction (Just idx) $ I.RuleAct $ R.Nix pth) [typicon "trash"] ]
        rulebinder v = inline "rulebinder" [localrule v, miniTurnstile]
        rns' = map (Prop.raise (length sks)) rns ++ lcls
        ctx' = reverse sks ++ ctx
        numberedAssumptions numbers assumptions = context (intersperse comma $ zipWith renderPropLabelled numbers assumptions)
        renderPropLabelled i p = labelledBrackets (renderProp ctx' ruleDOs p) (localrule i)
        
    metabinder' pth i n = case selected of
                             Just (R.ProofBinderFocus pth' i', n) | pth == pth', i == i' -> [metabinderEditor pth i n] 
                             _ -> [button "proofMB" (SetFocus $ ItemFocus idx $ I.RuleFocus $ R.ProofBinderFocus pth i) [ metabinder n ]]
    metabinderEditor pth i n = form_ [ class_ "mbEditor", onSubmit (ItemAction (Just idx) $ I.RuleAct $ R.RenameProofBinder pth i) ] 
                                     [ expandingTextbox "mbeditor" UpdateInput n
                                     , submitButton "confirmButton" [typicon "tick-outline"]
                                     , button "cancelButton" Reset [typicon "times-outline"] 
                                     , focusHack "mbeditor"
                                     ]

    
    goalButton pth = if Just (R.GoalFocus pth) == fmap fst selected then 
                        focusedButton "selectedGoal" (SetFocus $ ItemFocus idx $ I.RuleFocus $ R.GoalFocus pth) [typicon "location"]
                     else 
                        button "goal" (SetFocus $ ItemFocus idx $ I.RuleFocus $ R.GoalFocus pth) [typicon "location-outline"]

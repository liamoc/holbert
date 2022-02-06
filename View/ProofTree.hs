{-# LANGUAGE OverloadedStrings #-}
module View.ProofTree where
import Miso
import qualified Miso.String as MS
import Data.List (intersperse)
import Data.Maybe (isNothing, isJust, fromMaybe)
import DisplayOptions
import qualified Item as I
import qualified Rule as R
import qualified Prop as P
import ProofTree
import View.Prop
import View.Utils
import View.Term
import View.Paragraph (renderText)


renderProofTree opts pt tbl selected textIn = renderPT False False [] [] [] pt
  where
    
    termDOs = tDOs opts
    ruleDOs = RDO {termDisplayOptions = termDOs, showInitialMetas = True, ruleStyle = Turnstile}
    renderRR (P.Rewrite r fl) = span_ [class_ "rule-rulename-rewrite"]  [renderRR r, sup_ [] [if not fl then "→" else "←"]]
    renderRR (P.Elim r i) = span_ [class_ "rule-rulename-elim"] [renderRR r, sup_ [] [renderRR i]]
    renderRR (P.Defn d) = definedrule d
    renderRR (P.Local i) = localrule i

    currentGS = case selected of 
      Just (R.ProofFocus t g) -> g 
      _ -> Nothing

    renderPT inTree showPreamble rns ctx pth (PT ptopts sks lcls prp msgs) =
      let binders = (if showMetaBinders opts then concat (zipWith (metabinder' pth) [0 ..] sks) else [])
                 ++ boundrules
          boundrules = if assumptionsMode opts == Hidden then map rulebinder [length rns .. length rns + length lcls - 1] else []       
          premises = case msgs of
            Just (rr, sgs) -> zipWith (renderPT (inTree || shouldBeTree) (isJust ptopts) rns' ctx') (map (: pth) [0 ..]) sgs
            Nothing        -> []
          spacer = maybe (goalButton pth) (const $ "") msgs

          ruleTitle = Just $ maybe "?" (addNix . renderRR . fst) msgs


          subtitleWidget = case selected of
              Just (R.ProofFocus (R.SubtitleFocus pth') _) | pth == pth' -> editor "expanding" (R.SetSubgoalHeading pth) txt  
              _ -> button "editable editable-heading" "" (SetFocus (R.ProofFocus (R.SubtitleFocus pth) currentGS)) (renderText tbl txt)
            where txt = case ptopts of Nothing -> "Subgoal"; Just opts -> subtitle opts

          preamble = div_ [class_ "word-proof-prop"] 
            $ (div_ [class_ "proof-subtitle"] [subtitleWidget] :)
            
            $ [ multi boundrules, renderPropNameLabelledE (Just $ case assumptionsMode opts of
              New  -> map P.Local [length rns ..]
              Cumulative -> map P.Local [0..]
              _ -> []) (Just pth) (InProofTree (selected, textIn)) Nothing ctx (ruleDOs {ruleStyle = compactRules opts}) 
                           $ P.Forall sks (case assumptionsMode opts of
              New  -> lcls
              Cumulative -> rns'
              _ -> []) prp ]
          conclusion = pure $ renderPropNameLabelledE (Just $ case assumptionsMode opts of
              New  -> map P.Local [length rns ..]
              Cumulative -> map P.Local [0..]
              _ -> []) Nothing (InProofTree (selected, textIn)) Nothing ctx' ruleDOs
                           $ P.Forall [] (case assumptionsMode opts of
              New  -> lcls
              Cumulative -> rns'
              _ -> []) prp
       in multi $ (if inTree || not showPreamble then id else (preamble:) )                
                $ (if inTree || showPreamble then id else (span_ [class_ "item-rule-proofheading"] ["Proof", if not shouldShowWords then ". " else "" ] :) )
                $ (if inTree || not shouldShowWords then id else (multi [" by ", fromMaybe "" ruleTitle, spacer, if null premises then ". " else ": "]  :))
                $ (if inTree || shouldShowWords || not showPreamble then id else ("by: ":))
                $ (if inTree then id else (styleButton :))
                $ pure $ (if shouldShowWords then wordsrule else inferrule binders) premises spacer ruleTitle conclusion

      where
        styleButton = if shouldShowWords then 
                        iconButton "grey" "Switch to tree style" "tree" (Act $ R.ToggleStyle pth)
                      else 
                        iconButton "grey" "Switch to prose style" "flow-children" (Act $ R.ToggleStyle pth)
        shouldShowWords = not inTree && not shouldBeTree
        shouldBeTree = case ptopts of Nothing -> True; Just opts -> not (proseStyle opts)
        addNix t = multi [t, iconButton "red" "Delete proof subtree" "trash" (Act $ R.Nix pth)]

        rulebinder v = multi [localrule v, miniTurnstile]

        rns' = map (P.raise (length sks)) rns ++ lcls
        ctx' = reverse sks ++ ctx


    metabinder' pth i n = case selected of
      Just (R.ProofFocus (R.ProofBinderFocus pth' i') _) | pth == pth', i == i' -> [metabinderEditor pth i textIn]
      _ -> [button "editable editable-math" "" (SetFocus $ R.ProofFocus (R.ProofBinderFocus pth i) currentGS) [metabinder n]]

    metabinderEditor pth i n = editor "expanding" (R.RenameProofBinder pth i) n

    goalButton pth  = case selected of
      Just (R.ProofFocus _ (Just (R.GS _ _ _ pth' _)))  | pth == pth' -> focusedButton "button-icon button-icon-active button-icon-goal" "" (Act $ R.SelectGoal pth) [typicon "location"]
      _ -> button "button-icon button-icon-blue button-icon-goal" "Unsolved goal" (Act $ R.SelectGoal pth) [typicon "location-outline"]

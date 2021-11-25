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
    renderRR (P.Rewrite r) = multi ["->", renderRR r]
    renderRR (P.Defn d) = definedrule d
    renderRR (P.Local i) = localrule i
    renderRR (P.Transitivity) = "trans"

    renderPT inTree showPreamble rns ctx pth (PT ptopts sks lcls prp msgs) =
      let binders = (if showMetaBinders opts then concat (zipWith (metabinder' pth) [0 ..] sks) else [])
                 ++ boundrules
          boundrules = if assumptionsMode opts == Hidden then map rulebinder [length rns .. length rns + length lcls - 1] else []       
          premises = case msgs of
            Just (rr, sgs) -> zipWith (renderPT (inTree || (shouldBeStyle == Tree)) (isJust ptopts) rns' ctx') (map (: pth) [0 ..]) sgs
            Nothing        -> []
          spacer = maybe (goalButton pth) (const $ "") msgs

          ruleTitle = Just $ maybe "?" (addNix . renderRR . fst) msgs

          conclusionTerm = renderTermCtxEditable 
              (Just 
                ( textIn
                , R.MetavariableFocus
                , R.InstantiateMetavariable
                , selected
                )) ctx' termDOs prp

          subtitleWidget
            | selected == Just (R.ProofSubtitleFocus pth) = editor "expanding" (R.SetSubgoalHeading pth) txt  
            | otherwise = button "editable editable-heading" "" (SetFocus (R.ProofSubtitleFocus pth)) (renderText tbl txt)
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
                $ (if inTree then id else (multi [styleButton, equationalButton] : ))
                $ pure $ (case shouldBeStyle of {Prose -> wordsrule; Tree -> inferrule binders; Equational -> equationalrule binders}) premises spacer ruleTitle conclusion

      where
        styleButton = if notTree then 
                        iconButton "grey" "Switch to tree style" "tree" (Act $ R.ToggleStyle pth)
                      else 
                        iconButton "grey" "Switch to prose style" "flow-children" (Act $ R.ToggleStyle pth)
        equationalButton = if (shouldBeStyle == Tree || shouldBeStyle == Prose) && True then
                        iconButton "grey" "Switch to equational style" "equals-outline" (Act $ R.ToggleEquational pth)
                      else if (shouldBeStyle == Equational)  then
                        iconButton "grey" "Switch to tree style" "tree" (Act $ R.ToggleEquational pth)
                      else
                        button_ [class_ "button-icon button-icon-grey", type_ "button", title_ "Cannot apply equational style"] [typicon "equals-outline"] 
                        --iconButton "black" "Cannot apply equational style" "tree" --(do nothing)
                        
        shouldShowWords = notTree && not (shouldBeStyle == Equational)
        notTree = not inTree && not (shouldBeStyle == Tree)
        shouldBeStyle = case ptopts of Nothing -> Tree; Just opts -> toggleStyle (proofStyle opts)
        isTransitive = case msgs of
          Just (P.Transitivity, sgs) -> True
          _ -> False
        addNix t = multi [t, iconButton "red" "Delete proof subtree" "trash" (Act $ R.Nix pth)]

        rulebinder v = multi [localrule v, miniTurnstile]

        rns' = map (P.raise (length sks)) rns ++ lcls
        ctx' = reverse sks ++ ctx


    metabinder' pth i n = case selected of
      Just (R.ProofBinderFocus pth' i') | pth == pth', i == i' -> [metabinderEditor pth i textIn]
      _ -> [button "editable editable-math" "" (SetFocus $ R.ProofBinderFocus pth i) [metabinder n]]

    metabinderEditor pth i n = editor "expanding" (R.RenameProofBinder pth i) n

    goalButton pth  = case selected of
      Just (R.GoalFocus pth True) -> focusedButton "button-icon button-icon-active button-icon-goal" "" (SetFocus $ R.GoalFocus pth True) [typicon "location"]
      Just (R.GoalFocus pth False) -> focusedButton "button-icon button-icon-active button-icon-goal" "" (SetFocus $ R.GoalFocus pth False) [typicon "location"]
      _ -> button "button-icon button-icon-blue button-icon-goal" "Unsolved goal" (SetFocus $ R.GoalFocus pth False) [typicon "location-outline"]

flatten :: ProofTree -> [ProofTree]
flatten (PT opts sks lcls g (Just (P.Transitivity, [a,b]))) = concatMap flatten [a,b]--case opts of
--  Nothing -> concatMap flatten [a,b]
--  Just opts -> case proofStyle opts of
--    Equational -> concatMap flatten [a,b]
--      _ -> concatMap flatten [a,b]
flatten (PT opts sks lcls g mgs) = [(PT opts sks lcls g mgs)]


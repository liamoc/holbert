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
import qualified Terms as T
import ProofTree
import View.Prop
import View.Utils
import View.Term
import View.Paragraph (renderText)


renderProofTree opts pt tbl selected textIn = renderPT False False False False [] [] [] pt
  where
    
    termDOs = tDOs opts
    ruleDOs = RDO {termDisplayOptions = termDOs, showInitialMetas = True, ruleStyle = Turnstile}
    renderRR (P.Rewrite r fl bb) = span_ [class_ "rule-rulename-rewrite"]  [renderRR r, sup_ [] [if not fl then "→" else "←"]]
    renderRR (P.Elim r i) = span_ [class_ "rule-rulename-elim"] [renderRR r, sup_ [] [renderRR i]]
    renderRR (P.Distinctness n) = span_ [class_ "rule-rulename-elim"] [builtinrule "disjoint", sup_ [] [renderRR n]]
    renderRR (P.Injectivity) = builtinrule "inject"
    renderRR (P.Defn d) = definedrule d
    renderRR (P.Local i) = localrule i
    renderRR (P.Cases n i) = casesrule n i
    renderRR (P.Induction n i) = inductrule n i
    renderRR P.Refl = builtinrule "refl"
    renderRR P.Transitivity = builtinrule "trans"

    currentGS = case selected of 
      Just (R.ProofFocus t g) -> g 
      _ -> Nothing

    renderPT inTree inAbbr showPreamble inCalcAbbr rns ctx pth thePT@(PT ptopts sks lcls prp msgs) =
      let binders = (if showMetaBinders opts && not showPreamble then concat (zipWith (metabinder' pth) [0 ..] sks) else [])
                 ++ boundrules
          boundrules = if assumptionsMode opts == Hidden && not showPreamble then map rulebinder [length rns .. length rns + length lcls - 1] else []       
          premises = case msgs of
            Just (rr, sgs) -> (if hideFirstPremise then (text "…":) . drop 1 else id) $ 
                              zipWith (renderPT (inTree || shouldBeTree) (inAbbr || shouldBeAbbr) (isJust ptopts) inCalcAbbr rns' ctx') (map (: pth) [0 ..]) sgs
            Nothing        -> []
          hideFirstPremise = case fmap fst msgs of 
            Just (P.Rewrite r fl (Just d)) -> inCalcAbbr
            _ -> False
          spacer = maybe (goalButton pth) (const $ "") msgs

          ruleTitle = Just $ maybe "?" ((if inAbbr || shouldBeAbbr then id else addNix) . renderRR . fst) msgs


          subtitleWidget = case selected of
              Just (R.ProofFocus (R.SubtitleFocus pth') _) | pth == pth' -> editor "expanding" (R.SetSubgoalHeading pth) txt  
              _ -> button "editable editable-heading" "" (SetFocus (R.ProofFocus (R.SubtitleFocus pth) currentGS)) (renderText tbl txt)
            where txt = case ptopts of Nothing -> "Show:"; Just opts -> subtitle opts


          wordboundrules [] [] = []
          wordboundrules [] [(lab,c)] = [div_ []  [ span_ [class_ "item-rule-proofheading"] ["Assuming "], renderRR lab, ": ",renderPropNameE (InProofTree (selected,textIn)) Nothing ctx' ruleDOs c ]]
          wordboundrules [] ls = [div_ [class_ "item-rule-proofheading"] ["Assuming:"], ul_ [] (map (\(lab,c)-> li_ [] [renderRR lab, ": ", renderPropNameE (InProofTree (selected,textIn)) Nothing ctx' ruleDOs c]) ls)]
          wordboundrules vars [] = [div_ []  [ span_ [class_ "item-rule-proofheading"] ("Given " : concat (zipWith (metabinder' pth) [0 ..] vars)) ]]
          wordboundrules vars [(lab,c)] = [div_ []  [ span_ [class_ "item-rule-proofheading"] ("Given " : concat (zipWith (metabinder' pth) [0 ..] vars)), span_ [class_ "item-rule-proofheading"] [" where "], renderRR lab, ": ",renderPropNameE (InProofTree (selected,textIn)) Nothing ctx' ruleDOs c ]]
          wordboundrules vars ls = [div_ []  [ span_ [class_ "item-rule-proofheading"] ("Given " : concat (zipWith (metabinder' pth) [0 ..] vars)), span_ [class_ "item-rule-proofheading"] [" where:"], ul_ [] (map (\(lab,c)-> li_ [] [renderRR lab, ": ", renderPropNameE (InProofTree (selected,textIn)) Nothing ctx' ruleDOs c]) ls)]]
          preamble = div_ [class_ "word-proof-prop"] 
            $ (div_ [class_ "proof-subtitle"] [multi (wordboundrules (if showMetaBinders opts then sks else []) $ zip (map P.Local [length rns ..]) lcls)] :)
            $ (div_ [] [subtitleWidget]:)
            $ [div_ [class_ "word-proof-goal"] [ renderPropNameE (InProofTree (selected, textIn)) Nothing ctx' ruleDOs $ P.Forall [] [] prp ] ]

          conclusion = pure $ renderPropNameLabelledE (Just $ case assumptionsMode opts of
              New | not showPreamble || inTree -> map P.Local [length rns ..]
              Cumulative | not showPreamble || inTree -> map P.Local [0..]
              _ -> []) Nothing (InProofTree (selected, textIn)) Nothing ctx' ruleDOs
                           $ P.Forall [] (case assumptionsMode opts of
              New  | not showPreamble || inTree -> lcls
              Cumulative | not showPreamble || inTree -> rns'
              _ -> []) prp
       in if inAbbr then 
            multi [fromMaybe "" ruleTitle, spacer, if null premises then "" else multi $ ["("] ++ intersperse ", " premises ++ [")"] ]
          else if fmap style ptopts == Just Calc && not inTree then 
            let (a1, bs) = fmap removeRefls (flatten thePT pth)
             in multi 
                [ if showPreamble then "" else (span_ [class_ "item-rule-proofheading"] ["Proof. "])
                , preamble
                , if showPreamble then "by: " else "", styleButton
                , table_ 
                    [ intProp "cellpadding" 2, class_ "equational-proof",intProp "cellspacing" 2]
                    ([ tr_ []
                      $  [td_ [class_ "rule-cell rule-binderbox"] [renderPropNameE (InProofTree (selected, textIn)) Nothing ctx' ruleDOs $ P.Forall [] [] a1]]
                      ++ [td_ [class_ "rule-cell rule-spacer"] ["  ", button "button-style" "Normalise" (Act $ R.NormaliseEquality pth) ["Normalise"]]]
                      ++ [td_ [class_ "rule-cell rule-rulebox"] ["   "]]
                      ++ [td_ [class_ "rule-cell rule-empty"] [" "]]
                      ++ [td_ [class_ "rule-cell rule-empty"] [" "]]
                    ] ++ map (renderEqPT ctx') bs)
                ]
          else if fmap style ptopts == Just Abbr && not inTree then
            multi $ (if showPreamble then id else (span_ [class_ "item-rule-proofheading"] ["Proof. "] :) )
                  $ (preamble:)
                  $ (" by ":)
                  $ ((if isNothing msgs then id else addNix) (multi [fromMaybe "" ruleTitle, spacer, if null premises then "." else multi $ ["("] ++ intersperse ", " premises ++ [")"] ]):)
                  $ [styleButton]
          else if shouldShowWords then 
            multi $ (if showPreamble then id else (span_ [class_ "item-rule-proofheading"] ["Proof. "] :) )
                  $ (preamble:)
                  $ (multi [" by ", fromMaybe "" ruleTitle, spacer, if null premises then ". " else ": "]  :)
                  $ (styleButton :)
                  $ pure $ wordsrule premises 
          else 
            multi $ (if inTree || not showPreamble then id else (preamble:) )                
                  $ (if inTree || showPreamble then id else (span_ [class_ "item-rule-proofheading"] ["Proof. " ] :) )
                  $ (if inTree || not showPreamble then id else ("by: ":))
                  $ (if inTree then id else (styleButton :))
                  $ pure $ inferrule binders premises spacer ruleTitle conclusion                

      where
        renderEqPT :: [T.Name] -> (T.Term, ProofTree, Path) -> View (LocalAction R.RuleFocus R.RuleAction)
        renderEqPT ctx (g, pt, pth) = tr_ []
                          $  [td_ [class_ "rule-eq-cell"] [" "]]
                          ++ [td_ [class_ "rule-eq-cell rule-eq-equals"] [" = "]]
                          ++ [td_ [class_ "rule-eq-cell rule-eq-term"] [renderPropNameE (InProofTree (selected, textIn)) Nothing ctx' ruleDOs $ P.Forall [] [] g ]]
                          ++ [td_ [class_ "rule-eq-cell rule-eq-ref"] [renderPT False True False True rns ctx pth pt]]
                          ++ [td_ [class_ "rule-eq-cell rule-eq-nix"] [ iconButton "red" "Delete proof step" "trash" (Act $ R.Nix pth)]]

        wordsrule [p] =  div_ [class_ "word-proof"] [p]
        wordsrule premises = 
          div_ [class_ "word-proof"] [ ul_ [] $ map (li_ [] . pure) premises ]
        styleButton = div_ [class_ "proof-style-menu"] 
                           [ div_ [class_ "proof-style-menu-options"] 
                                  [ if not shouldBeTree then button "button-style" "Switch to tree style"  (Act $ R.SetStyle pth Tree) ["Tree"] else "" 
                                  , if not shouldShowWords || shouldBeAbbr then button "button-style" "Switch to prose style"  (Act $ R.SetStyle pth Prose) ["Prose"] else ""
                                  , if not shouldBeAbbr then button "button-style" "Switch to summary style" (Act $ R.SetStyle pth Abbr) ["Summary"] else "" 
                                  , button "button-style" "Switch to calculational style" (Act $ R.SetStyle pth Calc) ["Calc"] ]
                           , iconButton "grey" "Switch proof style" "brush" Noop ]
        shouldShowWords = not inTree && not shouldBeTree
        shouldBeTree = case ptopts of Nothing -> True; Just opts -> style opts == Tree 
        shouldBeAbbr = case ptopts of Nothing -> False; Just opts -> not inTree && style opts == Abbr 
        addNix t = multi [t, iconButton "red" "Delete proof subtree" "trash" (Act $ R.Nix pth)]

        rulebinder v = multi [localrule v, miniTurnstile]

        rns' = map (P.raise (length sks)) rns ++ lcls
        ctx' = reverse sks ++ ctx


    metabinder' pth i n = case selected of
      Just (R.ProofFocus (R.ProofBinderFocus pth' i') _) | pth == pth', i == i' -> [metabinderEditor pth i textIn]
      _ -> [button "editable editable-math" "" (SetFocus $ R.ProofFocus (R.ProofBinderFocus pth i) currentGS) [metabinder n]]

    metabinderEditor pth i n = editor "expanding" (R.RenameProofBinder pth i) n

    goalButton pth  = case selected of
      Just (R.ProofFocus _ (Just (R.GS _ _ _ pth' _)))  | pth == pth' -> focusedButton "button-icon button-icon-active button-icon-goal" "" (Act $ R.SelectGoal pth False) [typicon "location"]
      _ -> button "button-icon button-icon-blue button-icon-goal" "Unsolved goal" (Act $ R.SelectGoal pth False) [typicon "location-outline"]


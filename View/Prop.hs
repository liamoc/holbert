{-# LANGUAGE OverloadedStrings #-}
module View.Prop where
import Miso
import qualified Miso.String as MS
import Editor (TermDisplayOptions(..),RuleStyle (..))
import qualified Rule as R
import Terms
import Prop
import View.Utils
import View.Term

data RuleDisplayOptions = RDO { termDisplayOptions :: TermDisplayOptions, showInitialMetas :: Bool, ruleStyle :: RuleStyle } 

renderProp = renderPropName Nothing
renderPropName = renderPropNameE Nothing

renderPropNameE editable n ctx opts prp = renderP (showInitialMetas opts) n (ruleStyle opts) ctx [] prp
  where
    metabinders pth vs = wrap $
      zipWith (metabinder' pth) [0 ..] vs ++
        case editable of
          Just (selected, n) -> case selected of
            Just (R.NewRuleBinderFocus pth') | pth == pth' -> [editor "expanding" (R.AddRuleBinder pth) n]
            Just (R.RuleTermFocus pth') | pth == pth' ->
                [ iconButton "blue button-icon-addbinder" "Add Variable" "plus" (SetFocus $ R.NewRuleBinderFocus pth)
                , inline "metabinder" ["."]
                ]
            _ -> []
          _ -> []
      where
        wrap [] = multi []
        wrap cs = inline "rule-binders" cs

    metabinder' pth i n = case editable of
      Just (selected, n') ->
        editableMath n' (metabinder n) (R.RuleBinderFocus pth i) (R.RenameRuleBinder pth i)
          [iconButton "red" "Remove Variable" "trash" (Act $ R.DeleteRuleBinder pth i)]
          selected
      Nothing -> metabinder n

    renderTerm' ctx pth trm = case editable of
      Just (selected, n) ->
        editableMath n (renderTermCtx ctx (termDisplayOptions opts) trm) (R.RuleTermFocus pth) (R.UpdateTerm pth)
          (if null pth then [] else [iconButton "red" "Delete Premise" "trash" (Act $ R.DeletePremise pth)])
          selected
      Nothing -> renderTermCtx ctx (termDisplayOptions opts) trm

    renderRR' rr@(Local n) = renderRR rr
    renderRR' rr@(Defn n) = case editable of
      Just (selected, n) -> editableMath n (renderRR rr) R.NameFocus R.Rename [] selected
      Nothing -> renderRR rr

    renderRR (Defn d) = definedrule d
    renderRR (Local i) = localrule i

    isSelectedOrBinders pth = case editable of
      Just (selected, n) -> case selected of
        Just (R.RuleTermFocus pth')      | pth == pth' -> True
        Just (R.RuleBinderFocus pth' _)  | pth == pth' -> True
        Just (R.NewRuleBinderFocus pth') | pth == pth' -> True
        _ -> False
      _ -> False

    isSelected pth = fmap fst editable == Just (Just (R.RuleTermFocus pth))

    renderP showMetas title style ctx pth (Forall sks lcls g) =
      let (renderer, nextStyle) = case style of
            Bar -> (inferrule, Dots)
            BarTurnstile -> (inferrule, Turnstile)
            Turnstile -> (entailment (isSelected pth), Turnstile)
            Dots -> (hypothetical (isSelected pth), Turnstile)
          ctx' = reverse sks ++ ctx
          renderNext pth prp | style /= Turnstile = renderP True Nothing nextStyle ctx' pth prp
          renderNext pth prp@(Forall [] [] g) | not (isSelectedOrBinders pth) = renderP True Nothing nextStyle ctx' pth prp
          renderNext pth prp = multi (parenthesise [renderP True Nothing nextStyle ctx' pth prp])
          binders = if showMetas then [metabinders pth sks] else []
          premises = zipWith renderNext (map (: pth) [0 ..]) lcls
          spacer =
            if isSelected pth
              then iconButton "blue button-icon-addpremise" "Add Premise" "plus-outline" (Act $ R.AddPremise pth)
              else ""
          ruleTitle = fmap renderRR' title
          conclusion = [renderTerm' ctx' pth g]
       in renderer binders premises spacer ruleTitle conclusion


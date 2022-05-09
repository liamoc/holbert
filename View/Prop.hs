{-# LANGUAGE OverloadedStrings #-}
module View.Prop where
import Miso
import qualified Miso.String as MS
import DisplayOptions
import qualified Rule as R
import Terms
import Prop
import View.Utils
import View.Term

data RuleDisplayOptions = RDO { termDisplayOptions :: TermDisplayOptions, showInitialMetas :: Bool, ruleStyle :: RuleStyle } 

data EditableMode = NotEditable
                  | Editable (Maybe R.RuleFocus) Bool MS.MisoString --boolean "is this deletable?"
                  | InProofTree (Maybe (R.RuleFocus), MS.MisoString)

renderProp = renderPropName Nothing
renderPropName = renderPropNameE NotEditable
renderPropNameE = renderPropNameLabelledE Nothing Nothing

renderPropNameLabelledE labels ptpath editable n ctx opts prp = renderP labels (showInitialMetas opts) n (ruleStyle opts) ctx [] prp
  where
    metabinders pth vs = wrap $
      zipWith (metabinder' pth) [0 ..] vs ++
        case editable of
          Editable selected deletable n -> case selected of
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

    currentGS = case editable of 
      InProofTree (Just (R.ProofFocus _ g), _) -> g
      _ -> Nothing

    metabinder' pth i n = case editable of
      Editable selected _ n' ->
        editableMath n' (metabinder n) (R.RuleBinderFocus pth i) (R.RenameRuleBinder pth i)
          [iconButton "red" "Remove Variable" "trash" (Act $ R.DeleteRuleBinder pth i)]
          selected
      InProofTree (selected, n') | pth == [], Just pth' <- ptpath ->
        editableMath n' (metabinder n) (flip R.ProofFocus currentGS $ R.ProofBinderFocus pth' i) (R.RenameProofBinder pth' i)
          [] selected
      _ -> metabinder n

    renderTerm' ctx pth trm = case editable of
      Editable selected _ n ->
        editableMath n (renderTermCtx ctx (termDisplayOptions opts) trm) (R.RuleTermFocus pth) (R.UpdateTerm pth)
          (if null pth then [] else [iconButton "red" "Delete Premise" "trash" (Act $ R.DeletePremise pth)])
          selected
      InProofTree (selected, n) ->
        renderTermCtxEditable (Just (n, flip R.ProofFocus currentGS . R.MetavariableFocus, R.InstantiateMetavariable, selected)) ctx (termDisplayOptions opts) trm
      _ -> renderTermCtx ctx (termDisplayOptions opts) trm

    renderRR' rr@(Defn nm) = case editable of
      Editable selected deletable n -> multi $ editableMath n (renderRR rr) R.NameFocus R.Rename [] selected : if deletable then [iconButton "red" "Delete axiom" "trash" (Act $ R.DeleteRI)] else []
      _ -> renderRR rr
    renderRR' rr = renderRR rr

    renderRR (Defn d) = definedrule d
    renderRR (Local i) = localrule i
    renderRR (Cases n i) = casesrule n i
    renderRR (Induction n i) = inductrule n i
    renderRR Refl = builtinrule "refl"

    isSelectedOrBinders pth = case editable of
      Editable selected _ n -> case selected of
        Just (R.RuleTermFocus pth')      | pth == pth' -> True
        Just (R.RuleBinderFocus pth' _)  | pth == pth' -> True
        Just (R.NewRuleBinderFocus pth') | pth == pth' -> True
        _ -> False
      _ -> False

    isSelected pth = case editable of 
      Editable (Just (R.RuleTermFocus pth')) _ _ -> pth == pth'  
      otherwise -> False      

    renderP labels showMetas title style ctx pth (Forall sks lcls g) =
      let (renderer, nextStyle) = case style of
            Bar -> (inferrule, Dots)
            BarTurnstile -> (inferrule, Turnstile)
            Turnstile -> (entailment (isSelected pth), Turnstile)
            Dots -> (hypothetical (isSelected pth), Turnstile)
          ctx' = reverse sks ++ ctx
          renderNext pth prp | style /= Turnstile = renderP Nothing True (labels >>= lookupMaybe (head pth)) nextStyle ctx' pth prp
          renderNext pth prp@(Forall [] [] g) | not (isSelectedOrBinders pth) = renderP Nothing True (labels >>= lookupMaybe (head pth)) nextStyle ctx' pth prp
          renderNext pth prp = multi (parenthesise [renderP Nothing True (labels >>= lookupMaybe (head pth)) nextStyle ctx' pth prp])
          lookupMaybe n [] = Nothing
          lookupMaybe 0 (x:xs) = Just x
          lookupMaybe n (x:xs) = lookupMaybe (n-1) xs
          binders = if showMetas then [metabinders pth sks] else []
          premises = zipWith renderNext (map (: pth) [0 ..]) lcls
          spacer =
            if isSelected pth
              then iconButton "blue button-icon-addpremise" "Add Premise" "plus-outline" (Act $ R.AddPremise pth)
              else ""
          ruleTitle = fmap renderRR' title
          conclusion = [renderTerm' ctx' pth g]
       in renderer binders premises spacer ruleTitle conclusion


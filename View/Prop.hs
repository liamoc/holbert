{-# LANGUAGE OverloadedStrings #-}
module View.Prop where
import Terms
import ProofTree
import Prop
import View.Utils
import View.Term
import Miso hiding (on)
import Data.List (intersperse, dropWhileEnd, groupBy)
import Control.Monad
import Editor (TermDisplayOptions(..),RuleStyle (..))
import qualified Miso.String as MS
import qualified Data.Map as M
import qualified Rule as R

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
                [ button "button-icon button-icon-blue button-icon-addbinder" (SetFocus $ R.NewRuleBinderFocus pth) [typicon "plus"]
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
          [button "button-icon button-icon-red" (Act $ R.DeleteRuleBinder pth i) [typicon "trash"]]
          selected
      Nothing -> metabinder n

    renderTerm' ctx pth trm = case editable of
      Just (selected, n) ->
        editableMath n (renderTermCtx ctx (termDisplayOptions opts) trm) (R.RuleTermFocus pth) (R.UpdateTerm pth)
          [button "button-icon button-icon-red" (Act $ R.DeletePremise pth) [typicon "trash"]]
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
              then button "button-icon button-icon-blue button-icon-addpremise" (Act $ R.AddPremise pth) [typicon "plus-outline"]
              else ""
          ruleTitle = fmap renderRR' title
          conclusion = [renderTerm' ctx' pth g]
       in renderer binders premises spacer ruleTitle conclusion


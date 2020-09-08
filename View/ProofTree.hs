{-# LANGUAGE OverloadedStrings #-}
module View.ProofTree where

import Terms
import Prop
import ProofTree
import View.Prop
import View.Utils
import View.Term
import Miso hiding (on)
import Data.List (intersperse, dropWhileEnd, groupBy)
import qualified Miso.String as MS
import qualified Data.Map as M
import qualified Item as I
import qualified Rule as R
import Editor (DisplayOptions (..), RuleStyle (..), AssumptionsMode (..))

renderProofTree opts pt selected = renderPT [] [] [] pt
  where
    termDOs = tDOs opts
    ruleDOs = RDO {termDisplayOptions = termDOs, showInitialMetas = True, ruleStyle = Turnstile}

    renderRR (Defn d) = definedrule d
    renderRR (Local i) = localrule i

    renderPT rns ctx pth (PT sks lcls prp msgs) =
      let binders = (if showMetaBinders opts then concat (zipWith (metabinder' pth) [0 ..] sks) else [])
                 ++ (if assumptionsMode opts == Hidden then map rulebinder [length rns .. length rns + length lcls - 1] else [])
          premises = case msgs of
            Just (rr, sgs) -> zipWith (renderPT rns' ctx') (map (: pth) [0 ..]) sgs
            Nothing        -> []
          spacer = maybe (goalButton pth) (const $ "") msgs

          ruleTitle = Just $ maybe "?" (addNix . renderRR . fst) msgs

          conclusionTerm = renderTermCtx ctx' termDOs prp

          conclusion = case assumptionsMode opts of
            New | not (null lcls) -> [numberedAssumptions [length rns ..] lcls, turnstile, conclusionTerm]
            Cumulative            -> [numberedAssumptions [0 ..] rns', turnstile, conclusionTerm]
            _                     -> [conclusionTerm]
       in inferrule binders premises spacer ruleTitle conclusion

      where
        addNix t = multi [t, button "button-icon button-icon-red" (Act $ R.Nix pth) [typicon "trash"]]

        rulebinder v = multi [localrule v, miniTurnstile]

        rns' = map (Prop.raise (length sks)) rns ++ lcls
        ctx' = reverse sks ++ ctx

        numberedAssumptions numbers assumptions = wrap (intersperse comma $ zipWith renderPropLabelled numbers assumptions)
          where wrap [] = multi []
                wrap cs = inline "rule-context" cs

        renderPropLabelled i p = labelledBrackets (renderProp ctx' ruleDOs p) (localrule i)

    metabinder' pth i n = case selected of
      Just (R.ProofBinderFocus pth' i', n) | pth == pth', i == i' -> [metabinderEditor pth i n]
      _ -> [button "editable editable-math" (SetFocus $ R.ProofBinderFocus pth i) [metabinder n]]

    metabinderEditor pth i n = editor "expanding" (R.RenameProofBinder pth i) n

    goalButton pth =
      if Just (R.GoalFocus pth) == fmap fst selected
      then focusedButton "button-icon button-icon-active button-icon-goal" (SetFocus $ R.GoalFocus pth) [typicon "location"]
      else button "button-icon button-icon-blue button-icon-goal" (SetFocus $ R.GoalFocus pth) [typicon "location-outline"]

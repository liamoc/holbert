{-# LANGUAGE OverloadedStrings, TupleSections #-}
module View.Rule where
import Miso
import qualified Miso.String as MS
import Optics.Core
import Data.Maybe (isNothing)
import Data.String
import View.Utils
import View.Prop
import View.ProofTree
import DisplayOptions
import qualified Item as I
import qualified Rule as R
import qualified ProofTree as PT
import qualified Prop as P
import qualified Controller as C
import qualified Editor as E

renderRule i opts tbl textIn selected (R.R ruleType ris) = div_ []
  $ case ruleType of
    R.Axiom ->  axiomHeading i
              : (if selected == Just (R.AddingRule) then editor "newrule" R.AddRule textIn else multi [])
              : zipWith (\n (R.RI name prop mpt) -> fmap (wrapping n) $ block "rule" [renderPropNameE (Editable (selected >>= unwrapping n, textIn)) (Just (P.Defn name)) [] ruleDOs prop, block "axiom-options" [getName name, button_ [class_ "button-axiom button-icon button-icon-red", type_ "button", title_ "Delete axiom"] [typicon "trash"]]] ) [0..] ris
    R.InductionInit ->  inductionHeading
              : block "" []
              : inductionInitHeading i
              : (if selected == Just (R.AddingRule) then editor "newrule" R.AddRule textIn else multi [])
              : zipWith (\n (R.RI name prop mpt) -> fmap (wrapping n) $ block "rule" [inline "" [renderPropNameE (Editable (selected >>= unwrapping n, textIn)) (Just (P.Defn name)) [] ruleDOs prop, block "axiom-options" [getName name, button_ [class_ "button-axiom button-icon button-icon-red", type_ "button", title_ "Delete axiom"] [typicon "trash"]]]] ) [0..] ris
    R.InductionPrinc -> inductionPrincHeading i
                      : (if selected == Just (R.AddingRule) then editor "newrule" R.AddRule textIn else multi [])
                      : zipWith (\n (R.RI name prop mpt) -> fmap (wrapping n) $ block "rule" [inline "" [renderPropNameE (Editable (selected >>= unwrapping n, textIn)) (Just (P.Defn name)) [] ruleDOs prop, block "axiom-options" [getName name, button_ [class_ "button-axiom button-icon button-icon-red", type_ "button", title_ "Delete axiom"] [typicon "trash"]]]] ) [0..] ris
    R.Theorem -> theoremHeading i
                  : zipWith (\n (R.RI name prop mpt) -> 
                    fmap (wrapping n) $ multi $ case mpt of
                      Just ps ->  block "rule" [renderPropNameE (Editable (selected >>= unwrapping n, textIn)) (Just (P.Defn name)) [] ruleDOs prop]
                                : block "item-rule-proofbox" [renderProofTree opts (ps ^. R.proofTree) tbl (selected >>= unwrapping n)  textIn]
                                : []
                      Nothing ->  []
                  ) [0..] ris 
                   
  where
    ruleDOs = RDO { termDisplayOptions = tDOs opts, showInitialMetas = showMetaBinders opts, ruleStyle = compactRules opts }
    wrapping :: Int -> LocalAction R.RuleFocus R.RuleAction -> LocalAction (R.Focus R.Rule) (R.Action R.Rule) 
    wrapping i = mapLocalAction (R.RF i) (R.RA i)
    unwrapping :: Int -> R.Focus R.Rule -> Maybe R.RuleFocus
    unwrapping n (R.RF i rf) = if n == i then Just rf else Nothing
    unwrapping n R.AddingRule = Nothing
    getName ::  MS.MisoString -> View (LocalAction R.RuleFocus R.RuleAction)
    getName ruleName = fromString (MS.fromMisoString ruleName)
    

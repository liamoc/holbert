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

renderRule i opts tbl textIn selected rules@(R.R ruleType ris rest) = div_ [class_ classname]
  $ case ruleType of
    R.Axiom ->  axiomHeading i (case ris of [_] -> ""; _ -> "s") 
              : zipWith (\n (R.RI ruleName prop mpt) -> fmap (wrapping n) 
                          $ block "rule axiom" [renderPropNameE (Editable (selected >>= unwrapping n) True textIn) (Just (P.Defn ruleName)) [] ruleDOs prop] )
                  [0..] ris
             ++ [block "rule axiom addition" $ pure $ if selected == Just (R.AddingRule) then editor "newrule" R.AddRule textIn else iconButton "blue" "Insert new rule" "plus-outline" (SetFocus $ R.AddingRule)]
    R.Theorem -> theoremHeading i
               : zipWith (\n (R.RI name prop mpt) -> 
                 fmap (wrapping n) $ multi $ case mpt of
                   Just ps ->  block "rule" [renderPropNameE (Editable (selected >>= unwrapping n) False textIn) (Just (P.Defn name)) [] ruleDOs prop]
                             : block "item-rule-proofbox" [renderProofTree opts (ps ^. R.proofTree) tbl (selected >>= unwrapping n)  textIn]
                             : []
                   Nothing ->  []
               ) [0..] ris 
    R.Inductive ->  inductiveHeading i
              : zipWith (\n (R.RI ruleName prop mpt) -> fmap (wrapping n) 
                          $ block ("rule " <> classToUse <> if P.isIntroduction prop then "" else " not-intro-error") [renderPropNameE (Editable (selected >>= unwrapping n) True textIn) (Just (P.Defn ruleName)) [] ruleDOs prop] )
                  [0..] ris
             ++ [block ("rule addition " <> classToUse) $ pure $ if selected == Just (R.AddingRule) then editor "newrule" R.AddRule textIn else iconButton "blue" "Insert new rule" "plus-outline" (SetFocus $ R.AddingRule)]
             ++ [collapsableblock (MS.pack $ show i) ["Derived Rules"] $ map (\(name,p) -> block ("rule " <> classToUse) [fmap (wrapping undefined) $ renderPropName (Just name) [] ruleDOs p]) rest]
                   
  where
    classname = case ruleType of R.Axiom -> "item-rule-axiom-set"; R.Inductive -> "item-rule-axiom-set"; _ -> "item-rule-theorem-box"
    ruleDOs = RDO { termDisplayOptions = tDOs opts, showInitialMetas = showMetaBinders opts, ruleStyle = compactRules opts }
    wrapping :: Int -> LocalAction R.RuleFocus R.RuleAction -> LocalAction (R.Focus R.Rule) (R.Action R.Rule) 
    wrapping i = mapLocalAction (R.RF i) (R.RA i)
    unwrapping :: Int -> R.Focus R.Rule -> Maybe R.RuleFocus
    unwrapping n (R.RF i rf) = if n == i then Just rf else Nothing
    unwrapping n R.AddingRule = Nothing
    classToUse = case compactRules opts of Turnstile -> "axiom-block"; _ -> "axiom"
    

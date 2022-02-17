{-# LANGUAGE OverloadedStrings, TupleSections #-}
module View.Rule where
import Miso
import Optics.Core
import Data.Maybe (isNothing)
import View.Utils
import View.Prop
import View.ProofTree
import DisplayOptions
import qualified Item as I
import qualified Rule as R
import qualified ProofTree as PT
import qualified Prop as P

renderRule i opts tbl textIn selected (R.R ruleType name prop mpt) = div_ []
  $ case ruleType of
        R.Axiom -> axiomHeading i
                : [ block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop] ]
        R.Induction -> inductionHeading i
                        : block "" []
                        : block "item-rule-theoremheading" [anchor i ["Basis."]]
                        : block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop]
                        : block "item-rule-theoremheading" [anchor i ["Inducive Steps."]]
                        : block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop]
                        : block "item-rule-theoremheading" [anchor i ["Inductive Principle."]]
                        : [ block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop] ]
        R.Theorem -> theoremHeading i
                        : case mpt of
                            Just ps -> block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop]
                                      : [ block "item-rule-proofbox" [renderProofTree opts (ps ^. R.proofTree) tbl selected textIn] ]
  where
    ruleDOs = RDO { termDisplayOptions = tDOs opts, showInitialMetas = showMetaBinders opts, ruleStyle = compactRules opts }

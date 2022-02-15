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

-- started trying to have a seperate element for axiom and a set of axioms. needed or just have an axiom element with abritary # of axioms?
renderRule i opts tbl textIn selected (R.R name prop mpt) = div_ []
  $ (if isNothing mpt then axiomHeading else theoremHeading) i  -- if elif else for Axiom, AxiomSet and Theorem
  : block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop]
  : case mpt of 
      Just ps -> [ block "item-rule-proofbox" [renderProofTree opts (ps ^. R.proofTree) tbl selected textIn] ]
      Nothing -> [ block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop] ]
  where
    ruleDOs = RDO { termDisplayOptions = tDOs opts, showInitialMetas = showMetaBinders opts, ruleStyle = compactRules opts } 

-- 16: $ (if isNothing mpt then axiomHeading else theoremHeading) i
-- 19: Just ps -> [ block "item-rule-proofbox" [renderProofTree opts (ps ^. R.proofTree) tbl selected textIn] ]
-- 20: Nothing -> []

-- case elemType of 
--       Axiom -> []
--       AxiomSet -> [ block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop] ]  -- [] then recursively call a function that displays '+' and calls blankAxiom
--       Theorem ps -> [ block "item-rule-proofbox" [renderProofTree opts (ps ^. R.proofTree) tbl selected textIn] ]
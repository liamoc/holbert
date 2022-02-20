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
    R.Axiom ->  axiomHeading i
              : block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop]
              : []
    R.InductionInit ->  inductionHeading
                      : block "" []
                      : inductionInitHeadngDummy i R.InductionInit
                      : block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop]
                      : inductionPrincHeadingDummy i R.InductionPrinc
                      : []
    R.InductionPrinc ->   block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop]
                        : []
    R.Theorem -> theoremHeading i
                  : case mpt of
                      Just ps ->  block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop]
                                : block "item-rule-proofbox" [renderProofTree opts (ps ^. R.proofTree) tbl selected textIn]
                                : []
                      Nothing ->  []
  where
    ruleDOs = RDO { termDisplayOptions = tDOs opts, showInitialMetas = showMetaBinders opts, ruleStyle = compactRules opts }


-- R.Induction -> inductionHeading i
--                 : block "" []
--                 : basisSubheading i
--                 : block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop]
--                 : stepsSubheading i
--                 : block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop]
--                 :principleSubheading i
--                 : [ block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop] ]
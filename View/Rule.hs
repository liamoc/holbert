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

renderRule i opts textIn selected (R.R name prop mpt) = div_ []
  $ (if isNothing mpt then axiomHeading else theoremHeading) i
  : block "rule" [renderPropNameE (Editable (selected, textIn)) (Just (P.Defn name)) [] ruleDOs prop]
  : case mpt of 
      Just ps -> [ block "item-rule-proofbox" [renderProofTree opts (ps ^. R.proofTree) selected textIn] ]
      Nothing -> []
  where
    ruleDOs = RDO { termDisplayOptions = tDOs opts, showInitialMetas = showMetaBinders opts, ruleStyle = compactRules opts } 
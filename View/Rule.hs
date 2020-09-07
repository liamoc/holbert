{-# LANGUAGE OverloadedStrings, TupleSections #-}
module View.Rule where
import Miso hiding (on)
import qualified Miso.String as MS
import View.Utils
import View.Prop
import View.ProofTree
import Editor (DisplayOptions (..))
import qualified Item as I
import qualified Rule as R
import qualified ProofTree as PT
import Control.Monad
import Optics.Core
import Data.Maybe

renderRule i opts textIn selected (R.R name prop mpt) = div_ []
           $ (if isNothing mpt then axiomHeading else theoremHeading) i
           : block "rule" [renderPropNameE (Just (selected, textIn)) (Just (PT.Defn name)) [] ruleDOs prop]
           : case mpt of 
               Just ps -> 
                 [ proofHeading
                 , block "item-rule-proofbox" [renderProofTree opts (ps ^. R.proofTree) (fmap (, textIn) selected)]
                 ]
               Nothing ->  []
  where
    ruleDOs = RDO { termDisplayOptions = tDOs opts, showInitialMetas = showMetaBinders opts, ruleStyle = compactRules opts } 
    proofHeading = block "item-rule-proofheading" ["Proof."]

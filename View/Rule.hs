{-# LANGUAGE OverloadedStrings #-}
module View.Rule where
import Miso hiding (on)
import qualified Miso.String as MS
import View.Utils
import View.Prop
import View.ProofTree
import Editor
import qualified Item as I
import qualified Rule as R
import qualified ProofTree as PT
import Control.Monad
import Optics.Core
import Data.Maybe

renderRule opts textIn selected i (R.R name prop mpt) = div_ []
           $ (if isNothing mpt then axiomHeading else theoremHeading) i
           : block "rule" [renderPropNameE (Just (i,selected,textIn)) (Just (PT.Defn name)) [] ruleDOs prop]
           : case mpt of 
               Just ps ->  [proofHeading, 
                           div_ [class_ "item-rule-proofbox"] [renderProofTree opts i (ps ^. R.proofTree) 
                                (case selected of
                                    ItemFocus j (I.RuleFocus f) -> guard (i == j) >> pure (f, textIn)
                                    _ -> Nothing)]]
               Nothing ->  []
  where
    ruleDOs = RDO { termDisplayOptions = tDOs opts , showInitialMetas = showMetaBinders opts, showEmptyTurnstile = False, ruleStyle = compactRules opts } 
    proofHeading = div_ [class_ "item-rule-proofheading"] [text "Proof."]

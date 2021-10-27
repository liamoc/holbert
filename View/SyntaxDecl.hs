{-# LANGUAGE OverloadedStrings #-}

module View.SyntaxDecl where
import Miso
import qualified Miso.String as MS
import qualified SyntaxDecl as SD
import View.Term
import View.Utils

renderSyntaxDecl i opts tbl textIn selected (SD.SyntaxDecl n p a tbl2) = div_ []
  $ (block "item-syntaxdecl" [anchor i ["SyntaxDecl."]])
  : button "editable editable-name" "" (SetFocus SD.NameFocus) [anchor i [text n]]
  : button "editable editable-prec" "" (SetFocus SD.PrecFocus) [anchor i [text $ MS.toMisoString $ show p]]
  : [button "editable editable-assoc" "" (SetFocus SD.AssocFocus) [anchor i [text $ MS.toMisoString $ show a]]]
{-# LANGUAGE OverloadedStrings #-}
module View.SyntaxDecl where 
import Miso
import qualified Miso.String as MS
import qualified SyntaxDecl as S
import View.Term
import View.Utils

renderSyntaxDecl i textIn selected (S.SyntaxDecl l n assoc) = 
    div_ [class_ "item-syntax"] [syntaxDeclHeading i, 
      case selected of
        Just _ -> editor "expanding" S.Edit textIn
        _ -> button "editable" "" (SetFocus S.Select) (name n)
    ]
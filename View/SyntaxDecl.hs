{-# LANGUAGE OverloadedStrings #-}
module View.SyntaxDecl where 
import Miso
import qualified Miso.String as MS
import qualified SyntaxDecl as S
import View.Term
import View.Utils
import StringRep (Associativity(..))

renderSyntaxDecl i textIn selected (S.SyntaxDecl l n assoc) = 
    div_ [class_ "item-syntax"] [syntaxDeclHeading i, 
      case selected of
        Just S.SelectName -> editor "expanding" S.EditName textIn
        _ -> button "editable" "" (SetFocus S.SelectName) (name n)
    , select_ [class_ "editable", onChange (Act . S.SetAssoc . toAssoc) ] 
      [ option_ [value_ "none", selected_ (assoc == NonAssoc)] ["(no associativity)"]
      , option_ [value_ "left", selected_ (assoc == LeftAssoc)] ["(left associative)"]
      , option_ [value_ "right", selected_ (assoc == RightAssoc)] ["(right associative)",rawHtml "&nbsp;"]
      ]
    , div_ [class_ "item-syntax-precedence"] 
           ["(precedence level "
           , case selected of
               Just S.SelectPrec -> editor "number" S.EditPrec textIn
               _ -> button "editable" "" (SetFocus S.SelectPrec) [text $ MS.pack (show l)]
           , ")"]
    ]


toAssoc :: MS.MisoString -> Associativity
toAssoc "left" = LeftAssoc
toAssoc "right" = RightAssoc
toAssoc _ = NonAssoc

{-# LANGUAGE OverloadedStrings #-}
module View.SyntaxDecl where 
import Miso
import qualified Miso.String as MS
import qualified SyntaxDecl as S
import View.Term
import View.Utils
import StringRep (Associativity(..))

renderSyntaxDecl i textIn selected (S.SyntaxDecl ls) = 
    div_ [] (syntaxDeclHeading i: zipWith (\j itm -> renderSyntaxDecl' i j textIn selected itm alone) [0..] ls ++ 
            [ iconButton "blue" "Insert new notation" "plus-outline" (Act $ S.AddDecl) ])
  where
    alone = length ls == 1

renderSyntaxDecl' i j textIn selected (l, n, assoc) alone = 
    div_ [class_ $ if alone then "item-syntax item-syntax-single" else "item-syntax"] [
      case selected of
        Just (S.SelectName j') | j == j' -> editor "expanding" (S.EditName j) textIn
        _ -> button "editable" "" (SetFocus (S.SelectName j)) (name n)
    , select_ [class_ "editable", onChange (Act . flip S.SetAssoc j . toAssoc) ] 
      [ option_ [value_ "none", selected_ (assoc == NonAssoc)] ["(no associativity)"]
      , option_ [value_ "left", selected_ (assoc == LeftAssoc)] ["(left associative)"]
      , option_ [value_ "right", selected_ (assoc == RightAssoc)] ["(right associative)",rawHtml "&nbsp;"]
      ]
    , div_ [class_ "item-syntax-precedence"] 
           ["(precedence level "
           , case selected of
               Just (S.SelectPrec j') | j == j' -> editor "number" (S.EditPrec j) textIn
               _ -> button "editable" "" (SetFocus (S.SelectPrec j)) [text $ MS.pack (show l)]
           , ")"]
    , div_ [class_ "item-syntax-controls"]
           (if alone then [] else [ iconButton "red" "Delete notation" "trash" (Act $ S.RemoveDecl j)  ])
    ]


toAssoc :: MS.MisoString -> Associativity
toAssoc "left" = LeftAssoc
toAssoc "right" = RightAssoc
toAssoc _ = NonAssoc

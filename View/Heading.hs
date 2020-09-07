{-# LANGUAGE OverloadedStrings #-}
module View.Heading where
import Miso hiding (on)
import qualified Miso.String as MS
import View.Utils
import View.Term
import Editor
import qualified Item as I
import qualified Heading as H

renderHeading textIn selected i (H.Heading l txt) = case selected of 
   ItemFocus i' (I.HeadingFocus _) | i == i' ->
       anchor i [ form_ [ class_ ("editor editor-heading h" <> (MS.pack $ show l)), onSubmit (ItemAction (Just i) (I.HeadingAct H.Edit) ) ]
                        [ textbox "hdeditor" UpdateInput textIn
                        , submitButton "button-icon button-icon-blue" [typicon "tick-outline"]
                        , button "button-icon button-icon-grey" Reset [typicon "times-outline"] 
                        , focusHack "hdeditor"
                        ]]
   _ -> button "editable editable-heading" (SetFocus (ItemFocus i (I.HeadingFocus H.Select)))
       [case l of 0 -> h1_ [] [anchor i [text txt]]
                  1 -> h2_ [] [anchor i [text txt]]
                  2 -> h3_ [] [anchor i [text txt]]
                  3 -> h4_ [] [anchor i [text txt]]
                  _ -> h5_ [] [anchor i [text txt]]]

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
                            anchor i [ form_ [ class_ ("headingEditor h" <> (MS.pack $ show l)), onSubmit (ItemAction (Just i) (I.HeadingAct H.Edit) ) ]  $
                                     [ input_ [id_ "hdeditor", onInput (\s -> UpdateInput s), value_ textIn]
                                     , button_ [class_ "confirmButton" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     , script_ [] "document.getElementById('hdeditor').focus(); document.getElementById('hdeditor').select();"]]
                          _ -> button_ [ onClick (SetFocus (ItemFocus i (I.HeadingFocus H.Select))), class_ "headingButton" ] 
                                                [case l of 0 -> h1_ [] [anchor i [ text txt]]
                                                           1 -> h2_ [] [anchor i [ text txt]]
                                                           2 -> h3_ [] [anchor i [ text txt]]
                                                           3 -> h4_ [] [anchor i [ text txt]]
                                                           _ -> h5_ [] [anchor i [ text txt]]]

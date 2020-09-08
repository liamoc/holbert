{-# LANGUAGE OverloadedStrings #-}

module View.Heading where
import Miso
import qualified Miso.String as MS
import qualified Heading as H
import View.Term
import View.Utils

renderHeading i textIn selected (H.Heading l txt) = case selected of
  Just _ -> anchor i [editor ("heading h" <> (MS.pack $ show l)) H.Edit textIn]
  _ -> button "editable editable-heading" (SetFocus H.Select)
    [ case l of
        0 -> h1_ [] [anchor i [text txt]]
        1 -> h2_ [] [anchor i [text txt]]
        2 -> h3_ [] [anchor i [text txt]]
        3 -> h4_ [] [anchor i [text txt]]
        _ -> h5_ [] [anchor i [text txt]]
    ]
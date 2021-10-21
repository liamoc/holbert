{-# LANGUAGE OverloadedStrings #-}
module View.Paragraph where
import Miso 
import DisplayOptions
import StringRep as SR
import qualified Item as I
import qualified Miso.String as MS
import qualified Paragraph as P
import View.Term
import View.Utils

renderText tbl txt = normalText txt
  where
    normalText txt = case MS.span (`notElem` ("~/$*" :: String)) txt of
      (first, crest) | MS.null crest -> [text first]
      (first, crest) | Just (c, rest) <- MS.uncons crest -> text first : case MS.span (/= c) rest of
        (rfirst, crest') | MS.null rfirst, Just (_, rest') <- MS.uncons crest' -> text (MS.pack [c]) : normalText rest'
        (rfirst, crest') | MS.null crest' -> tagsFor c rfirst
        (rfirst, crest') | Just (_, rest') <- MS.uncons crest' -> tagsFor c rfirst ++ normalText rest'

    tagsFor '~' txt = [code_ [] [text txt]]
    tagsFor '/' txt = [i_ [] [text txt]]
    tagsFor '*' txt = [b_ [] [text txt]]
    tagsFor '$' txt =
      let (ctx, txt') = case MS.span (/= ':') txt of
            (_, crest) | MS.null crest -> ([], txt)
            (ctx, crest) | Just (_, rest) <- MS.uncons crest -> (MS.words ctx, rest)
       in case SR.parse tbl ctx txt' of
            Left _ -> ["$", text txt, "$"]
            Right t -> [inline "inline-math" [renderTermCtx ctx (TDO True True) t]]

renderParagraph tbl textIn selected (P.Paragraph txt) =
  block "" $ case selected of
    Just P.Select ->
      [ block "item-options-bottom"
        [ iconButton "blue" "Confirm edits" "tick-outline" (Act P.Edit)
        , iconButton "grey" "Cancel edits" "times-outline" Reset
        ]
      , expandingTextarea "ta" "paragraph" UpdateInput textIn
      ]
    Nothing ->
      [ block "item-options-bottom"
        [ iconButton "blue" "Edit paragraph" "edit" (SetFocus P.Select)]
      , block "paragraph" (renderText tbl txt)
      ]            
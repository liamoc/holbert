{-# LANGUAGE OverloadedStrings #-}
module View.Paragraph where
import Miso 
import Editor (TermDisplayOptions (..))
import StringRep
import qualified Item as I
import qualified Miso.String as MS
import qualified Paragraph as P
import View.Term
import View.Utils

renderText txt = normalText txt
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
            (ctx, crest) | Just (_, rest) <- MS.uncons crest -> (map MS.unpack (MS.words ctx), rest)
       in case fromSexps ctx (MS.unpack txt') of
            Left _ -> ["$", text txt, "$"]
            Right t -> [inline "inline-math" [renderTermCtx ctx (TDO True True) t]]

renderParagraph textIn selected (P.Paragraph txt) =
  block "" $ case selected of
    Just P.Select ->
      [ block "item-options-bottom"
        [ button "button-icon button-icon-blue" (Act P.Edit) [typicon "tick-outline"]
        , button "button-icon button-icon-grey" Reset [typicon "times-outline"]
        ]
      , expandingTextarea "ta" "paragraph" UpdateInput textIn
      ]
    Nothing ->
      [ block "item-options-bottom"
        [button "button-icon button-icon-blue" (SetFocus P.Select) [typicon "edit"]]
      , block "paragraph" (renderText txt)
      ]            
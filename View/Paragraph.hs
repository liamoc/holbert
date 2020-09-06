{-# LANGUAGE OverloadedStrings #-}
module View.Paragraph where
import Miso hiding (on)
import qualified Miso.String as MS
import qualified Paragraph as P
import View.Utils
import View.Term
import Editor
import qualified Item as I
import StringRep

renderText txt = normalText txt
  where
     normalText txt = case MS.span (`notElem` ("~/$*" :: String)) txt of 
                        (first,crest) | MS.null crest  -> [text first]
                        (first,crest) | Just (c,rest) <- MS.uncons crest -> text first : case MS.span (/= c) rest of
                                  (rfirst,crest') | MS.null rfirst, Just (_,rest') <- MS.uncons crest'-> text (MS.pack [c]) : normalText rest'
                                  (rfirst,crest') | MS.null crest' -> tagsFor c rfirst
                                  (rfirst,crest') | Just (_, rest') <- MS.uncons crest' ->  tagsFor c rfirst ++ normalText rest'
     tagsFor '~' txt = [code_ [][text txt]]
     tagsFor '/' txt = [i_ [][text txt]]
     tagsFor '*' txt = [b_ [][text txt]]
     tagsFor '$' txt = let (ctx, txt') = case MS.span (/= ':') txt of
                                         (_,crest) | MS.null crest   -> ([],txt)
                                         (ctx,crest) | Just (_,rest) <- MS.uncons crest -> (map MS.unpack (MS.words ctx), rest)
                        in case fromSexps ctx (MS.unpack txt') of
                             Left _ ->  [text "$", text txt, text "$"]
                             Right t -> [span_ [class_ "inlineMath"] [renderTermCtx ctx (TDO True True) t]]

renderParagraph textIn selected i (P.Paragraph txt) = 
   block "paragraphBlock" $ case selected of 
      ItemFocus i' (I.ParagraphFocus _) | i == i' ->
         [ block "moreItemOptions" 
            [ button "confirmButton" (ItemAction (Just i) (I.ParagraphAct P.Edit)) [typicon "tick-outline"]
            , button "cancelButton" Reset [ typicon "times-outline"]
            ]
         , expandingTextarea "ta" "paragraph" UpdateInput textIn
         ]
      _ -> [ block "moreItemOptions" 
              [ button "editButton" (SetFocus (ItemFocus i (I.ParagraphFocus P.Select))) [typicon "edit"]]
           , block "paragraph" (renderText txt)
           ] 

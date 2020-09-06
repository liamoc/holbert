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
                             Left _ -> [text "$", text txt, text "$"]
                             Right t -> [span_ [class_ "inlineMath"][renderTermCtx ctx (TDO True True) t]]

renderParagraph textIn selected i (P.Paragraph txt) = div_ [] $ (div_ [class_ "moreItemOptions"] $ 
                                case selected of 
                                  ItemFocus i' (I.ParagraphFocus _) | i == i' -> [
                                       button_ [class_ "confirmButton", onClick (ItemAction (Just i) (I.ParagraphAct P.Edit)) ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     ]
                                  _ -> [button_ [class_ "editButton", onClick (SetFocus (ItemFocus i (I.ParagraphFocus P.Select)))] [ span_ [class_ "typcn typcn-edit"] [] ]])
                           : (case selected of
                                ItemFocus i' (I.ParagraphFocus _) | i == i' ->
                                     [ textarea_ [ id_ "ta", onInput UpdateInput, class_ "paragraph"]  [text textIn]
                                     , script_ [] "it = document.getElementById('ta'); var fn = function() {  it.style.height=''; it.style.height = it.scrollHeight+'px'; }; window.setTimeout(fn,100); it.addEventListener('input',fn); it.focus();it.setSelectionRange(it.value.length, it.value.length);"
                                     ]
                                _ -> [div_ [class_ "paragraph"]  $ renderText txt] )
                   

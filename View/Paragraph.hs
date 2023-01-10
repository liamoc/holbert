{-# LANGUAGE OverloadedStrings #-}
module View.Paragraph where
import Miso 
import DisplayOptions
import StringRep as SR
import qualified Item as I
import qualified Miso.String as MS
import qualified Paragraph as P
import qualified Prop as P
import qualified Terms as T
import View.Term
import View.Utils
import View.Prop

renderText tbl txt = normalText txt
  where
    normalText txt = case MS.span (`notElem` ("~/$*^@" :: String)) txt of
      (first, crest) | MS.null crest -> [text first]
      (first, crest) | Just (c, rest) <- MS.uncons crest -> text first : case MS.span (/= c) rest of
        (rfirst, crest') | MS.null rfirst, Just (_, rest') <- MS.uncons crest' -> text (MS.pack [c]) : normalText rest'
        (rfirst, crest') | MS.null crest' -> tagsFor c rfirst
        (rfirst, crest') | Just (_, rest') <- MS.uncons crest' -> tagsFor c rfirst ++ normalText rest'

    tagsFor '^' txt | (ls, rs) <- MS.span (/= ':') txt, not (MS.null rs) = [sup_ [class_ "footnote"] [text ls, span_ [class_ "footnote-box"] (renderText tbl (MS.tail rs))]  ]
                    | otherwise = [text txt]
    tagsFor '~' txt = [code_ [] [text txt]]
    tagsFor '@' "goalTag" = [span_ [class_ "typcn typcn-location-outline inline-icon-example"] []]
    tagsFor '@' "entailment" = [turnstile]
    tagsFor '@' txt | (ls, rs) <- MS.span (/= '|') txt, not (MS.null rs) = 
                          if ls == "image" then [img_ [src_ (MS.tail rs)]] else [a_ [href_ (MS.tail rs)] [text ls]]
                    | otherwise = [a_ [href_ txt] [text txt]]
    tagsFor '/' txt = [i_ [] [text txt]]
    tagsFor '*' txt = [b_ [] [text txt]]
    tagsFor '$' txt = let spans = MS.span (/= ':') txt 
      in case spans of 
           (".thm", crest) | Just (_, rest) <- MS.uncons crest -> [inline "rule-rulename-defined" (name rest)]
           (".rule", crest) | Just (_, crest2) <- MS.uncons crest
                            , Just rule <- parseRule [] [] crest2 
                            -> [inline "inline-math" [fmap (const Noop) $ renderProp [] (RDO (TDO True True) True Turnstile) rule]]
           _ -> let (ctx, txt') = case spans of
                      (_, crest) | MS.null crest -> ([], txt)
                      (ctx, crest) | Just (_, rest) <- MS.uncons crest -> (MS.words ctx, rest)
                in case SR.parse tbl ctx txt' of
                     Left _ -> ["$", text txt, "$"]
                     Right t -> [inline "inline-math" [renderTermCtx ctx (TDO True True) t]]
    deparen "" = ""
    deparen str | MS.head str == '(' && MS.last str == ')' = deparen (MS.tail (MS.init str))
                | MS.head str == ' ' = deparen (MS.tail str)
                | MS.last str == ' ' = deparen (MS.init str)
                | otherwise = str
    parseRule ctx ctx' str | (name, rest) <- MS.span (/= '.') str 
                           , Nothing <- T.invalidName name
                           , Just ('.', rest') <- MS.uncons rest
                           = parseRule ctx (name:ctx') rest' 
    parseRule ctx ctx' str | Just (P.Forall [] lcls conc) <-  parseRule' (ctx' ++ ctx) str
                           = Just (P.Forall (reverse ctx') lcls conc)
    parseRule ctx ctx' str | Just (P.Forall [] [] conc) <-  parseRule'' (ctx' ++ ctx) str
                           = Just (P.Forall (reverse ctx') [] conc)
                           | otherwise = Nothing
    parseRule' ctx str | (body, rest) <- spanModuloParens (`notElem` [',','|']) str 
                      , Just (',', rest') <- MS.uncons rest
                      , Just l <- parseRule ctx [] (deparen body)
                      , Just (P.Forall [] lcls conc) <- parseRule' ctx rest'
                      = Just (P.Forall [] (l:lcls) conc )
    parseRule' ctx str | (body, rest) <- spanModuloParens (`notElem` [',','|']) str 
                      , Just ('|', rest') <- MS.uncons rest
                      , Just ('-', rest'') <- MS.uncons rest'
                      , Just l <- parseRule ctx [] body
                      , Right conc <- SR.parse tbl ctx rest''
                      = Just (P.Forall [] [l] conc)
                      | otherwise = Nothing
    parseRule'' ctx str | Right conc <- SR.parse tbl ctx str
                        = Just (P.Forall [] [] conc)
                        | otherwise = Nothing
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

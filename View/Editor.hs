{-# LANGUAGE OverloadedStrings #-}
module View.Editor where
import Miso
import qualified Miso.String as MS
import Editor
import DisplayOptions
import qualified Heading as H
import qualified Item as I
import qualified Paragraph as P
import qualified Rule as R
import qualified Terms as T
import Controller(definedSyntax)
import View.Item
import View.Term
import View.Prop
import View.Utils hiding (LocalAction (..))
import Data.List(mapAccumL)

version = "0.3.1"

data RuleType
  = Apply
  | Rewrite
  | ReverseRewrite


viewEditor :: Editor -> View EditorAction
viewEditor x =
  div_ [class_ "container", onKeyDown (\(KeyCode kc) -> if kc == 27 then Reset else Noop)] $
    [ div_ [class_ "document", id_ "document"]
      $ renderDoc (inputText x) (displayOptions x) (currentFocus x) (document x) ++ [block "document-endofcontent" []]
    , div_ [class_ "sidebar", id_ "sidebar"]
      $ toolbar
      : maybe id (\m -> (block "sidebar-errormessage" [text m] :)) (message x)
        [ block "sidebar-main" mainSidebar
        , renderDisplayOptions (displayOptions x)
        ]
    , script_ [] "Split(['#document','#sidebar'],{ sizes: [70,30], minSize:200});"
    ]
  where
    mainSidebar = case currentFocus x of
      ItemFocus i (I.RuleFocus (R.GoalFocus p rev)) ->
        [ div_ [class_ "tabbed"]
          [ input_ [type_ "radio", id_ "intro-tab", name_ "rulestabs", checked_ True]
          , input_ [type_ "radio", id_ "elim-tab", name_ "rulestabs"]
          , input_ [type_ "radio", id_ "rewrite-tab", name_ "rulestabs"]
          , ul_ [class_ "tabs"]
            [ li_ [class_ "tab"] [label_ [for_ "intro-tab"] ["Intro"]]
            , li_ [class_ "tab"] [label_ [for_ "elim-tab"] ["Elim"]]
            , li_ [class_ "tab"] [label_ [for_ "rewrite-tab"] ["Rewrite"]]
            ]
          , div_ [class_ "tab-content" ] (let (ctx, rs) = rulesSummary (i, p) (document x) in concatMap (renderPropGroup i p ctx Apply) rs)
          , div_ [class_ "tab-content" ] ["Incomplete"]
          , div_ [class_ "tab-content" ] (div_ [] [ input_ [checked_ (rev), id_ "rev_rewrite", type_ "checkbox", onChecked (\(Checked b) -> SetFocus (ItemFocus i (I.RuleFocus (R.GoalFocus p (b)))))]
        , label_ [for_ "rev_rewrite"] ["Reverse rewrite application"]
          ]:let (ctx, rs) = rulesSummary (i, p) (document x) in concatMap (renderPropGroup i p ctx (if rev then ReverseRewrite else Rewrite)) rs)
          
        ]]

      NewItemFocus i -> newItemMenu i
      ItemFocus i (I.ParagraphFocus _) -> editingHelp
      ImportFocus -> importForm
      CreditsFocus ->
        [ block "sidebar-header" ["Credits"]
        , block "sidebar-credits"
          [ a_ [class_ "big-icon-link", title_ "github", href_ "https://github.com/liamoc/holbert"] [typicon "social-github-circular" ]
          , a_ [class_ "big-icon-link", title_ "twitter", href_ "https://twitter.com/kamatsu8"] [typicon "social-twitter-circular" ]
          , p_ []
            [ "Holbert is made by "
            , a_ [href_ "http://liamoc.net"] ["Liam O'Connor"]
            , ", and several other student contributors."
            ]
          , p_ [] [" It is released under the BSD3 license."]
          , p_ [] ["Some icons are from the Typicons icon set by Stephen Hutchings."]
          , small_ [] ["This is version ", text version]
          ]
        ]
      _ -> [block "sidebar-header" ["Facts Summary:"], renderIndex $ document x]

    renderPropGroup i p ctx action (n, rs)=
      [ block "sidebar-header" [text n, text ":"]
      , block "sidebar-apply-group" $ map (renderAvailableRule ctx (displayOptions x) (i, p) action) rs
      ]

    toolbar = block "sidebar-logo"
      [ iconButton "teal" "Download document" "download-outline" Download
      , iconButton "teal" "Import from URL" "cloud-storage-outline" (SetFocus ImportFocus)
      , iconButton "grey" "About Holbert" "info-large-outline" (SetFocus CreditsFocus)
      , inline "logo-text" ["Holbert"]
      ]

    importForm =
      [ block "sidebar-header" ["Import from URL"]
      , editor' "importbox" Import UpdateInput Reset (inputText x)
      ]
    newItemMenu i = let insertHeading i n = InsertItem i (I.Heading (H.Heading n "")) in
      [ block "sidebar-header" ["Proof elements:"]
      , button "sidebar-insert" "" (SetFocus $ InsertingPropositionFocus False i) [block "item-rule-theoremheading" ["Axiom."]]
      , button "sidebar-insert" "" (SetFocus $ InsertingPropositionFocus True i) [block "item-rule-theoremheading" ["Theorem."]]
      , block "sidebar-header" ["Text elements:"]
      , button "sidebar-insert" "" (insertHeading i 1) [h2_ [] ["Heading 1"]]
      , button "sidebar-insert" "" (insertHeading i 2) [h3_ [] ["Heading 2"]]
      , button "sidebar-insert" "" (insertHeading i 3) [h4_ [] ["Heading 3"]]
      , button "sidebar-insert" "" (insertHeading i 4) [h5_ [] ["Heading 4"]]
      , button "sidebar-insert" "" (InsertItem i (I.Paragraph $ P.Paragraph "")) [block "sidebar-insert-paragraph" ["Paragraph"]]
      ]
    editingHelp =
      [ block "sidebar-header" ["Editing Help"]
      , table_ [class_ "sidebar-paragraph-editing"]
        [ tr_ []
          [ td_ [class_ "sidebar-paragraph-editing-lhs"] [code_ [] ["~codeSnippet()~"]]
          , td_ [] [code_ [] ["codeSnippet()"]]
          ]
        , tr_ []
          [ td_ [class_ "sidebar-paragraph-editing-lhs"] [code_ [] ["*bold text*"]]
          , td_ [] [b_ [] ["bold text"]]
          ]
        , tr_ []
          [ td_ [class_ "sidebar-paragraph-editing-lhs"] [code_ [] ["/italic text/"]]
          , td_ [] [i_ [] ["italic text"]]
          ]
        , tr_ []
          [ td_ [class_ "sidebar-paragraph-editing-lhs"] [code_ [] ["$_/\\_ A B$"]]
          , td_ [class_ "inline-math"] [renderTerm (TDO True True) $ T.Ap (T.Ap (T.Const "_/\\_") (T.Const "A")) (T.Const "B")]
          ]
        , tr_ []
          [ td_ [class_ "sidebar-paragraph-editing-lhs"] [code_ [] ["$A B:_/\\_ A B$"]]
          , td_ [class_ "inline-math"] $ pure $ renderTermCtx ["A", "B"] (TDO True True) (T.Ap (T.Ap (T.Const "_/\\_") (T.LocalVar 1)) (T.LocalVar 0))
          ]
        ]
      ]

renderIndex (_ : script) = ul_ [class_ "sidebar-index"] $ renderIndex' (zip [1 ..] script)
  where
    renderIndex' ((i, I.Heading (H.Heading lvl hd)) : scr)
      | (itms, rest) <- span (within lvl) scr =
        li_ [] [b_ [] [a_ [href_ $ "#anchor" <> (MS.pack $ show i)] [text hd]], ul_ [] $ renderIndex' itms] : renderIndex' rest
    renderIndex' ((i, I.Rule (R.R n _ mpt)) : scr) =
      li_ []
        [ a_ [href_ $ "#anchor" <> (MS.pack $ show i)] [definedrule n]
        , case mpt of
            Just ps
              | R.unresolved ps -> inline "sidebar-index-unsolved" [typicon "warning"]
              | otherwise -> inline "sidebar-index-solved" [typicon "input-checked"]
            Nothing -> span_ [] []
        ]
      : renderIndex' scr
    renderIndex' ((i, _) : scr) = renderIndex' scr
    renderIndex' [] = []
    within n (_, I.Heading (H.Heading lvl hd)) = lvl > n
    within n _ = True

renderDoc textIn opts selected script = snd $ mapAccumL go [] $ zip [0 ..] script
  where
    scriptSize = length script
    go tbl (i,item) =
      let mainItem = renderItem opts i tbl textIn item selected
          inserting = selected == NewItemFocus i
          itemOptions
            | i > 0 =
              block "item-options"
                $  [iconButton "red" "Delete element" "trash" (DeleteItem i)]
                ++ (if i > 1              then [iconButton "teal" "Shift element up" "arrow-up-outline" (ShiftDown $ i -1) ] else [])
                ++ (if i < scriptSize - 1 then [iconButton "teal" "Shift element down" "arrow-down-outline" (ShiftDown i) ] else [])
            | otherwise = ""
          insertButton =
            let (cls, icn) = if inserting
                  then ("insert button-icon-active", "plus")
                  else ("insert button-icon-blue", "plus-outline")
             in iconButton cls "Insert new element" icn (SetFocus $ NewItemFocus i)
                  : case selected of
                    InsertingPropositionFocus isT i' | i == i' ->
                      [editorWithTitle (if isT then theoremHeading i else axiomHeading i) "newrule" (InsertProposition i isT) UpdateInput Reset textIn]
                    _ -> []
       in (definedSyntax item ++ tbl, block (if inserting then "item item-inserting" else "item") $ [mainItem, itemOptions] ++ insertButton)

renderAvailableRule ctx opts (i, p) action (rr, r) =
  button "apply-option" "" (ItemAction (Just i) $ I.RuleAct $ a (rr, r) p)
    [fmap (const Noop) $ renderPropName (Just rr) ctx ruleDOs r]
  where
    ruleDOs = RDO {termDisplayOptions = tDOs opts, showInitialMetas = showMetaBinders opts, ruleStyle = compactRules opts}
    a = case (action) of
      Apply -> R.Apply
      Rewrite -> (R.Rewrite False)
      ReverseRewrite -> (R.Rewrite True)

renderDisplayOptions opts =
  form_ [class_ "sidebar-displayoptions"]
    [ div_ [class_ "sidebar-header"] ["Rule Format:"]
    , input_ [checked_ (compactRules opts == Turnstile), id_ "linear", type_ "radio", name_ "rules", onChecked (\_ -> ChangeDisplayOptions (opts {compactRules = Turnstile}))]
    , label_ [for_ "linear"] ["Linear"]
    , input_ [checked_ (compactRules opts == Bar), id_ "vertical", type_ "radio", name_ "rules", onChecked (\_ -> ChangeDisplayOptions (opts {compactRules = Bar}))]
    , label_ [for_ "vertical"] ["Vertical"]
    , input_ [checked_ (compactRules opts == BarTurnstile), id_ "mixture", type_ "radio", name_ "rules", onChecked (\_ -> ChangeDisplayOptions (opts {compactRules = BarTurnstile}))]
    , label_ [for_ "mixture"] ["Hybrid"]
    , div_ [class_ "sidebar-header"] ["Proof Tree Contexts:"]
    , input_ [checked_ (assumptionsMode opts == Hidden), type_ "radio", name_ "assumptions", id_ "assH", onChecked (\_ -> ChangeDisplayOptions (opts {assumptionsMode = Hidden}))]
    , label_ [for_ "assH"] ["Hidden"]
    , input_ [checked_ (assumptionsMode opts == New), type_ "radio", name_ "assumptions", id_ "assN", onChecked (\_ -> ChangeDisplayOptions (opts {assumptionsMode = New}))]
    , label_ [for_ "assN"] ["New Only"]
    , input_ [checked_ (assumptionsMode opts == Cumulative), type_ "radio", name_ "assumptions", id_ "assC", onChecked (\_ -> ChangeDisplayOptions (opts {assumptionsMode = Cumulative}))]
    , label_ [for_ "assC"] ["All"]
    , div_ [class_ "sidebar-header"] ["Display Options:"]
    , div_ []
        [ input_ [checked_ (showMetaBinders opts), id_ "showMB", type_ "checkbox", onChecked (\(Checked b) -> ChangeDisplayOptions (opts {showMetaBinders = b}))]
        , label_ [for_ "showMB"] ["Show Quantifiers"]
        ]
    , div_ []
        [ input_ [checked_ (showTeles (tDOs opts)), id_ "showTeles", type_ "checkbox", onChecked (\(Checked b) -> ChangeDisplayOptions (opts {tDOs = (tDOs opts) {showTeles = b}}))]
        , label_ [for_ "showTeles"] ["Show Metavariable Telescopes"]
        ]
    , div_ []
        [ input_ [checked_ (showInfixes (tDOs opts)), id_ "useInfix", type_ "checkbox", onChecked (\(Checked b) -> ChangeDisplayOptions (opts {tDOs = (tDOs opts) {showInfixes = b}}))]
        ,  label_ [for_ "useInfix"] ["Use Infix Notation"]
        ]
    ]

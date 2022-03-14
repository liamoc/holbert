{-# LANGUAGE OverloadedStrings #-}
module View.Editor where
import Miso
import qualified Miso.String as MS
import Editor
import DisplayOptions
import qualified Heading as H
import qualified Item as I
import qualified Paragraph as P
import qualified Prop as Prp
import qualified Rule as R
import qualified Terms as T
import Controller(definedSyntax)
import View.Item
import View.Term
import View.Prop
import View.Utils hiding (LocalAction (..))
import qualified View.Utils as U
import Data.List(mapAccumL)

version = "0.4.0"

data RuleType
  = Apply
  | Rewrite
  | ReverseRewrite
  | Elim

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
      ItemFocus i (I.RuleFocus foc@(R.RF currentRule (R.ProofFocus pf (Just gs@(R.GS binds locals t p rev))))) ->
        let tl = getRuleAt i (document x) in
        [ block "sidebar-header" ["Current Goal:"]
        , div_ [class_ "sidebar-goal-display"]
          [ div_ [class_ "sidebar-goal-buttons"] [iconButton (case pf of R.RewriteGoalFocus _ _ -> "active"; _ -> "teal" ) "Rewrite Goal" "equals-outline" 
                                                 $ (ItemAction (Just i) $ I.RuleAct $ R.RA currentRule $  R.RewriteGoal False) ] 
          , renderGoal currentRule (inputText x) i (Just foc) (displayOptions x) gs
          ]      
        ] ++ case pf of 
          R.GoalFocus rs -> 
            (if null locals then [] else 
              [ block "sidebar-header" ["Assumptions:"]
              , div_ [class_ "sidebar-assumptions"]  (map (renderAvailableRule' currentRule (map (\(_,_,n)->n) (reverse binds)) (displayOptions x) (i, p)) locals) 
              ]) ++
            [ block "sidebar-header" ["Available Rules:"]
            , div_ [class_ "sidebar-assumptions"] (map (renderAvailableRule currentRule [] (displayOptions x) (i,p)) rs)
            ]
          R.AssumptionFocus ix rs -> 
            [ block "sidebar-header" ["Assumption ", localrule ix,  
               iconButton "grey" "Close Assumption" "times-outline" (ItemAction (Just i) $ I.RuleAct $ R.RA currentRule $ R.SelectGoal p ) ]
            , div_ [class_ "sidebar-assumptions"]  [renderAvailableRule''  (map (\(_,_,n)->n) (reverse binds)) (displayOptions x) (i, p) $ fst (locals !! ix)]
            , block "sidebar-header" ["Available Eliminators:"]
            , div_ [class_ "sidebar-assumptions"] (map (renderAvailableRule currentRule [] (displayOptions x) (i,p)) rs)
            ]
          R.RewriteGoalFocus b rs -> 
            [ block "sidebar-header" ["Available Rewrites:",
               iconButton "grey" "Close Rewrites" "times-outline" (ItemAction (Just i) $ I.RuleAct $ R.RA currentRule $ R.SelectGoal p ) ]
            , div_ [class_ "sidebar-rewrite-box"] 
                      [ input_ [checked_ b, id_ "rev_rewrite", type_ "checkbox", onChecked (\(Checked b) -> ItemAction (Just i) $ I.RuleAct $ R.RA currentRule $ R.RewriteGoal b)]
                      , label_ [class_ "rewrite-checkbox-label", for_ "rev_rewrite"] ["Reverse rewrite application"]
                      ]
            , div_ [class_ "sidebar-assumptions"] (map (renderAvailableRule currentRule [] (displayOptions x) (i,p)) rs)
            ]
          _ -> []


        

      NewItemFocus i -> newItemMenu i
      ItemFocus i (I.ParagraphFocus _) -> editingHelp
      ImportFocus -> importForm
      InductionFocus i ->
        [ block "sidebar-header" ["Indcution elements: ",
            iconButton "grey" "Return to proof elements" "arrow-back-outline" (SetFocus $ NewItemFocus i) ]
        , button "sidebar-insert" "" (SetFocus $ InsertingPropositionFocus R.InductionInit i) [block "item-rule-theoremheading" ["Basis and Inductive Steps."]]
        , button "sidebar-insert" "" (SetFocus $ InsertingPropositionFocus R.InductionPrinc i) [block "item-rule-theoremheading" ["Inductive Principle"]]
        ]
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
      , button "sidebar-insert" "" (SetFocus $ InsertingPropositionFocus R.Axiom i) [block "item-rule-theoremheading" ["Axiom."]]
      , button "sidebar-insert" "" (SetFocus $ InductionFocus i) [block "item-rule-theoremheading" ["Induction Axioms."]]
      , button "sidebar-insert" "" (SetFocus $ InsertingPropositionFocus R.Theorem i) [block "item-rule-theoremheading" ["Theorem."]]
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
    renderIndex' ((i, I.Rule (R.R ruleType lst)) : scr) = map (\(R.RI n _ mpt) ->
      li_ []
        [ a_ [href_ $ "#anchor" <> (MS.pack $ show i)] [definedrule n]
        , case mpt of
            Just ps
              | R.unresolved ps -> inline "sidebar-index-unsolved" [typicon "warning"]
              | otherwise -> inline "sidebar-index-solved" [typicon "input-checked"]
            Nothing -> span_ [] []
        ]) lst ++ renderIndex' scr
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
                    InsertingPropositionFocus ruleType i' | i == i' ->
                      [editorWithTitle (if ruleType == R.Axiom then axiomHeading i
                                        else if ruleType == R.InductionInit then inductionInitEnter i
                                        else if ruleType == R.InductionPrinc then inductionPrincEnter i
                                        else theoremHeading i) "newrule" (InsertProposition i ruleType) UpdateInput Reset textIn]
                    _ -> []
       in (definedSyntax item ++ tbl, block (if inserting then "item item-inserting" else "item") $ [mainItem, itemOptions] ++ insertButton)

renderGoal currentRule textIn i selected opts gs@(R.GS sks _ t p b) = 
   fmap (toGlobalAction i . mapLocalAction I.RuleFocus I.RuleAct) $
     multi [ div_ [] (if (showMetaBinders opts) then concatMap metabinder' sks else []), div_ [class_ "sidebar-goal-conclusion"] 
        [renderTermCtxEditable 
          (Just 
            ( textIn
            , R.RF currentRule . flip R.ProofFocus (Just gs) . R.MetavariableFocus
            , R.RA currentRule . R.InstantiateMetavariable
            , selected
            )) (map (\(_,_,n) -> n) $ reverse sks) (tDOs opts) t]]
  where
    metabinder' (pth, i, n) = case selected of
      Just (R.RF m (R.ProofFocus (R.ProofBinderFocus pth' i') _)) | m == currentRule, pth == pth', i == i' -> [metabinderEditor pth i textIn]
      _ -> [button "editable editable-math" "" (U.SetFocus $ R.RF currentRule $ R.ProofFocus (R.ProofBinderFocus pth i) $ Just gs) [metabinder n]]

    metabinderEditor pth i n = editor "expanding" (R.RA currentRule $ R.RenameProofBinder pth i) n


renderAvailableRule currentRule ctx opts (i, p) ((rr, r), act) =
  div_ [class_ "apply-option", onClick (ItemAction (Just i) $ I.RuleAct $ R.RA currentRule $ act)]
       [fmap (const Noop) $ renderPropName (Just rr) ctx ruleDOs r]
  where
    ruleDOs = RDO {termDisplayOptions = tDOs opts, showInitialMetas = showMetaBinders opts, ruleStyle = compactRules opts}

renderAvailableRule' currentRule ctx opts (i, p) ((Prp.Local rr, r), act) =
    (case act of Just a -> div_ [class_ "apply-option", onClick (ItemAction (Just i) $ I.RuleAct $ R.RA currentRule a)]; 
                 _      -> div_ [class_ "inactive-assumption", onClick (ItemAction (Just i) $ I.RuleAct $ R.RA currentRule $ R.ExamineAssumption rr)])
      [fmap (const Noop) $ renderPropName (Just $ Prp.Local rr) ctx ruleDOs r]
  where
    ruleDOs = RDO {termDisplayOptions = tDOs opts, showInitialMetas = showMetaBinders opts, ruleStyle = compactRules opts}
renderAvailableRule' _ _ _ _ _ = multi []

renderAvailableRule'' ctx opts (i, p) (rr, r) =
      div_ [class_ "borderless-rule"] [fmap (const Noop) $ renderPropName (Just rr) ctx ruleDOs r]
  where
    ruleDOs = RDO {termDisplayOptions = tDOs opts, showInitialMetas = showMetaBinders opts, ruleStyle = compactRules opts}


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

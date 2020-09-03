-- | Haskell language pragma
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- | Haskell module declaration
module Main where

-- | Miso framework import
import Miso hiding (on)
import Miso.String hiding (zipWith, map, Ap, intersperse, length, dropWhileEnd, drop, span, null, filter, zip, reverse, concat, splitAt, concatMap, all, groupBy)
import qualified Miso.String as MS
import Terms
import Prop  hiding (addPremise)
import ProofTree
import Editor
import Data.Function (on)
import Data.List (intersperse, dropWhileEnd, groupBy)
import Data.Char (isDigit)
import Data.Maybe
import qualified Data.Set as S
import Data.Set (fromList)
import Debug.Trace
import Control.Monad.State
import System.Timeout
import Control.Exception
import StringRep
import qualified Data.Map as M
import Optics.Core
import qualified Rule as R 
import qualified Heading as H 
import qualified Paragraph as P 
import qualified Item as I
data RuleDisplayOptions = RDO { termDisplayOptions :: TermDisplayOptions, showInitialMetas :: Bool, ruleStyle :: RuleStyle, showEmptyTurnstile :: Bool } -- more later


main :: IO ()
main = startApp App {..}
  where
    initialAction = Reset
    model         = initialEditor
    update        = updateModel
    view          = viewModel
    events        = defaultEvents
    subs          = []
    mountPoint    = Nothing
    logLevel      = Off

-- | Updates model, optionally introduces side effects
updateModel :: EditorAction -> Editor -> Effect EditorAction Editor
updateModel act ed = noEff $ runAction act ed

-- | Constructs a virtual DOM from a model
viewModel :: Editor -> View EditorAction
viewModel x = div_ [class_ "topdiv", onKeyDown (\(KeyCode kc) -> if kc == 27 then Reset else Noop ) ] $
      [ div_ [class_ "mainpanel", id_ "mainpanel"] $ renderScript (inputText x) (displayOptions x) (currentFocus x) (document x) ++ [div_ [class_ "endofcontent"] []]
      , div_ [class_ "sidebar", id_ "sidebar"] $ logo:
          (case message x of 
              Just m ->  (div_ [class_ "errorMessage"] [text m]:)
              Nothing -> id) (div_ [class_ "sidebarmain"] (
          (case currentFocus x of 
             ItemFocus i (I.RuleFocus (R.GoalFocus p)) -> 
                    let (ctx, rs) = rulesSummary (i,p) (document x)
                     in concatMap (renderRuleGroup i p ctx) rs
             NewItemFocus i -> newItemMenu i
             ItemFocus i (I.ParagraphFocus _) -> editingHelp
             CreditsFocus -> div_ [class_ "insertItemHeader"] [text "Credits"]
                           : div_ [class_ "creditsText"] 
                                  [ text "Holbert is made by ", a_ [href_ "http://liamoc.net"] [text "Liam O'Connor"], text", a lecturer at the University of Edinburgh," 
                                  , text "using GHCJS and the Miso framework. Some icons are from the Typicons icon set by Stephen Hutchings."
                                  , text " It (will be) released under the BSD3 license."
                                  , text " Some code is based on work by Daniel Gratzer and Tobias Nipkow." 
                                  ]
                           : []
             _ -> [ div_ [class_ "insertItemHeader"] [text "Facts Summary:"],renderIndex (document x)]))
          :renderDisplayOptions (displayOptions x):[])
      , script_ [] "Split(['#mainpanel','#sidebar'],{ sizes: [70,30], minSize:200});"
      ]
  where 
        renderRuleGroup i p ctx (n,rs) = div_ [class_ "insertItemHeader"] [text $ pack (n ++ ":")]:
                [div_ [class_ "optionsGroup"] $ map (renderAvailableRule ctx (displayOptions x) (i,p)) rs]
        selectedGF x | ItemFocus i (I.RuleFocus (R.GoalFocus p)) <- currentFocus x = Just (i,p)
                     | otherwise = Nothing
        logo = div_ [class_ "logo", onClick (SetFocus CreditsFocus)] [small_ [] ["click for credits"], text "Holbert 0.1"]
        insertHeading i n = InsertItem i (I.Heading (H.Heading n ""))
        newItemMenu i = 
          [ div_ [class_ "insertItemHeader"] [text "Proof elements:"]
          , button_ [onClick (SetFocus $ InsertingPropositionFocus False i), class_ "insertItemOption" ] [div_ [class_ "axiomHeading"] ["Axiom."]]
          , button_ [onClick (SetFocus $ InsertingPropositionFocus True i ), class_ "insertItemOption" ] [div_ [class_ "theoremHeading"] ["Theorem."]]
          , div_ [class_ "insertItemHeader"] [text "Text elements:"]
          , button_ [onClick (insertHeading i 1), class_ "insertItemOption" ] [h2_ [] ["Heading 1"]]
          , button_ [onClick (insertHeading i 2), class_ "insertItemOption"] [h3_ [] ["Heading 2"]]
          , button_ [onClick (insertHeading i 3), class_ "insertItemOption"] [h4_ [] ["Heading 3"]]
          , button_ [onClick (insertHeading i 4), class_ "insertItemOption"] [h5_ [] ["Heading 4"]]
          , button_ [onClick (InsertItem i (I.Paragraph $ P.Paragraph "")), class_ "insertItemOption"] [div_ [class_ "parabutton"] ["Paragraph"]]
          ]
        editingHelp = 
         [ div_ [class_ "insertItemHeader"] [text "Editing Help"]
         , table_ [class_ "editingHelp"]
           [ tr_ [] 
             [ td_ [class_ "lhs"] [ code_ [] [text "~codeSnippet()~"] ]
             , td_ [] [ code_ [] [text "codeSnippet()"  ] ]
             ]
           , tr_ [] 
             [ td_ [class_ "lhs"] [ code_ [] [text "*bold text*"] ]
             , td_ [] [ b_    [] [text "bold text"  ] ]
             ]
           , tr_ [] 
             [ td_ [class_ "lhs"] [ code_ [] [text "/italic text/"] ]
             , td_ [] [ i_    [] [text "italic text"  ] ]
             ]
           , tr_ [] 
             [ td_ [class_ "lhs"] [code_ [] [text "$_/\\_ A B$"] ]
             , td_ [class_ "inlineMath"] $ pure $ renderTerm (TDO True True) (Ap (Ap (Const "_/\\_") (Const "A")) (Const "B"))
             ]
           , tr_ [] 
             [ td_ [class_ "lhs"] [code_ [] [text "$A B:_/\\_ A B$"] ]
             , td_ [class_ "inlineMath"] $ pure $ renderTermCtx ["A","B"] (TDO True True) (Ap (Ap (Const "_/\\_") (LocalVar 1)) (LocalVar 0))
             ]
           ] 
         ]

renderIndex (_:script) = ul_ [class_ "indexSummary"] $ renderIndex' (zip [1..] script)
  where
    renderIndex' ((i, I.Heading (H.Heading lvl hd)):scr) 
           | (itms, rest) <- span (within lvl) scr 
           = li_ [] [b_ [] [a_ [href_ $ "#anchor" <> (pack $ show i)] [text hd]], ul_ [] $ renderIndex' itms ] : renderIndex' rest
    renderIndex' ((i, I.Rule (R.R n _ mpt)):scr) 
           = li_ [] [ a_ [href_ $ "#anchor" <> (pack $ show i)] [renderRR $ Defn n]
                    , case mpt of 
                         Just ps | R.unresolved ps -> span_ [class_ "typcn typcn-warning outstandingGoalIndicator" ] []
                                 | otherwise  -> span_ [class_ "typcn typcn-input-checked noGoalIndicator" ] []
                         Nothing -> span_ [] []
                    ]:renderIndex' scr
    renderIndex' ((i, _):scr) = renderIndex' scr
    renderIndex' [] = []
    within n (_,I.Heading (H.Heading lvl hd)) = lvl > n
    within n _ = True
 


renderParagraph txt = normalText txt
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


renderScript textIn opts selected script = map (renderScriptItem textIn opts selected (length script)) (zip [0..] script)

renderScriptItem textIn opts selected scriptSize (i, item) = div_ [class_ $ if inserting then "itemBlock inserting" else "itemBlock"] $ [mainItem] ++ deleteButton:insertButton
  where
    mainItem = case item of 
      I.Rule (R.R name prop mpt) ->
         div_ []
           $ (if isNothing mpt then axiomHeading else theoremHeading) 
           : renderRuleNameE (Just (i,selected,textIn)) (Just (Defn name)) [] ruleDOs prop 
           : case mpt of 
               Just ps ->  [proofHeading, 
                           div_ [class_ "proofBox"] [renderProofTree opts i (ps ^. R.proofTree) 
                                (case selected of
                                    ItemFocus j (I.RuleFocus f) -> guard (i == j) >> pure (f, textIn)
                                    _ -> Nothing)]]
               Nothing ->  []
      I.Paragraph (P.Paragraph txt) -> div_ [] $ (div_ [class_ "moreItemOptions"] $ 
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
                                _ -> [div_ [class_ "paragraph"]  $ renderParagraph txt] )
                           
      I.Heading (H.Heading l txt) -> case selected of 
                          ItemFocus i' (I.HeadingFocus _) | i == i' ->
                            anchor i [ form_ [ class_ ("headingEditor h" <> (pack $ show l)), onSubmit (ItemAction (Just i) (I.HeadingAct H.Edit) ) ]  $
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
                                       
    ruleDOs = RDO { termDisplayOptions = tDOs opts , showInitialMetas = showMetaBinders opts, showEmptyTurnstile = False, ruleStyle = compactRules opts } 
    axiomHeading = div_ [class_ "axiomHeading"] [anchor i [text "Axiom."]]
    theoremHeading = div_ [class_ "theoremHeading"] [anchor i [text "Theorem."]]
    anchor i = a_ [id_ $ "anchor" <> pack (show i)]
    proofHeading = div_ [class_ "proofHeading"] [text "Proof."]
    deleteButton | i > 0 = div_ [class_ "itemOptions"] $
                                [ button_ [class_ "nix", onClick (DeleteItem i)] [span_ [class_ "typcn typcn-trash"] []]]
                             ++ (if i > 1 then [ button_ [class_ "movementButton", id_ $ "up" <> pack (show i) ,onClick (ShiftDown (i-1))] [span_ [class_ "typcn typcn-arrow-up-outline"] []]] else [])
                             ++ (if i < scriptSize - 1 then [button_ [class_ "movementButton", id_ $ "dn" <> pack (show i), onClick (ShiftDown i)] [span_ [class_ "typcn typcn-arrow-down-outline"] []]] else [])
                 | otherwise = span_ [] []
    inserting = selected == NewItemFocus i
    insertButton = let (cls,icn) = if inserting then ("insertButtonActive","typcn typcn-plus")
                                                else ("insertButton", "typcn typcn-plus-outline")
                   in button_ [class_ cls, onClick (SetFocus (NewItemFocus i))] [span_ [class_ icn] []]:
                      case selected of
                        InsertingPropositionFocus isT i' | i == i' -> pure $
                               form_ [ class_ "newRnEditor", onSubmit (InsertProposition i isT) ] 
                                     [ if isT then theoremHeading else axiomHeading
                                     , input_ [id_ "rneditor", style_ (M.singleton "width" (pack (show $ (((fromIntegral (MS.length textIn) + 1) *16) / 30)) <> "em")) 
                                              , onInput (\s -> UpdateInput s), value_ textIn]
                                     , button_ [class_ "confirmButton" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     , script_ [] "document.getElementById('rneditor').focus(); document.getElementById('rneditor').select();"]
                        _ -> []


renderAvailableRule ctx opts (i,p) (rr,r) 
     = button_ [class_ "ruleOption", onClick (ItemAction (Just i) $ I.RuleAct $ R.Apply (rr,r) p) ] [ renderRuleName (Just rr) ctx ruleDOs r]
  where
    ruleDOs = RDO { termDisplayOptions = tDOs opts , showInitialMetas = showMetaBinders opts, showEmptyTurnstile = False, ruleStyle = compactRules opts } 
  

renderDisplayOptions opts = 
  form_ [class_ "displayOptions"] 
       [ div_ [class_ "insertItemHeader"] [text "Rule Format:"]
       , input_ [checked_ (compactRules opts == Turnstile), id_ "linear", type_ "radio", name_ "rules", onChecked (\ _ -> ChangeDisplayOptions (opts { compactRules = Turnstile}) ) ]
       , label_ [for_ "linear"] [text "Linear" ]
       , input_ [checked_ (compactRules opts == Bar), id_ "vertical", type_ "radio", name_ "rules", onChecked (\ _ -> ChangeDisplayOptions (opts { compactRules = Bar }) ) ] 
       , label_ [for_ "vertical"] [text "Vertical" ]
       , input_ [checked_ (compactRules opts == BarTurnstile), id_ "mixture",type_ "radio", name_ "rules", onChecked (\ _ -> ChangeDisplayOptions (opts { compactRules = BarTurnstile}) ) ] 
       , label_ [for_ "mixture"] [text "Hybrid" ]
       , div_ [class_ "insertItemHeader"] [text "Proof Tree Contexts:"]
       , input_ [checked_ (assumptionsMode opts == Hidden),  type_ "radio", name_ "assumptions", id_ "assH", onChecked (\ _ -> ChangeDisplayOptions (opts { assumptionsMode = Hidden}) ) ]
       , label_ [for_ "assH"] [text "Hidden" ]
       , input_ [checked_ (assumptionsMode opts == New),  type_ "radio", name_ "assumptions", id_ "assN", onChecked (\ _ -> ChangeDisplayOptions (opts { assumptionsMode = New }) ) ] 
       , label_ [for_ "assN"] [text "New Only" ]
       , input_ [checked_ (assumptionsMode opts == Cumulative), type_ "radio", name_ "assumptions", id_ "assC", onChecked (\ _ -> ChangeDisplayOptions (opts { assumptionsMode = Cumulative}) ) ] 
       , label_ [for_ "assC"] [text "All" ]
       , div_ [class_ "insertItemHeader"] [text "Display Options:"]
       , div_ [] [ input_ [checked_ (showMetaBinders opts), id_ "showMB", type_ "checkbox", onChecked (\(Checked b) -> ChangeDisplayOptions (opts { showMetaBinders = b }))]
                 , label_ [for_ "showMB"] [text "Show Quantifiers" ]]
       , div_ [] [ input_ [checked_ (showTeles (tDOs opts)), id_ "showTeles", type_ "checkbox", onChecked (\(Checked b) -> ChangeDisplayOptions (opts { tDOs = (tDOs opts) {showTeles = b } }))]
                 , label_ [for_ "showTeles"] [text "Show Metavariable Telescopes" ]]
       , div_ [] [ input_ [checked_ (showInfixes (tDOs opts)), id_ "useInfix", type_ "checkbox", onChecked (\(Checked b) -> ChangeDisplayOptions (opts { tDOs = (tDOs opts) {showInfixes = b } }))]
                 , label_ [for_ "useInfix"] [text "Use Infix Notation" ]]
       ] 

renderTerm = renderTermCtx [] 
renderTermCtx context opts trm = renderTerm' True context trm
  where
    renderTerm' outer ctx (Lam (M v) t) = binder v (renderTerm' True (v:ctx) t)
    renderTerm' outer ctx other = renderTerm'' outer ctx other 

    renderTerm'' outer ctx t | Lam _ _ <- t = span_ [] $ parenthesise [renderTerm' False ctx t]
                             | (x, ts, []) <- peelApTelescope' t = case x of 
                                 LocalVar j 
                                      | j >= length ctx -> boundName (show j)
                                      | length ctx - j<= length context -> freevar (ctx !! j) -- , sub_ [] [text (pack $ show j)]]
                                      | otherwise -> boundName (ctx !! j)
                                 MetaVar i -> metavar i (renderITelescope ts)
                                 Const s -> constant s
                             | (Const n, [], args) <- peelApTelescope' t
                             , showInfixes opts
                             , length (filter (== '_') n) == length args = span_ [] $ (if outer then id else parenthesise) $ intersperse space (infixTerms n args)
                             | (x, ts, args) <- peelApTelescope' t = 
                                 span_ [] $ (if outer then id else parenthesise) $ renderTerm'' False ctx x : renderITelescope ts ++ space : intersperse space (map (renderTerm'' False ctx) args)
      where 
        parenthesise = ([span_ [class_ "parens"] [ text "("]] ++) . (++ [span_ [class_ "parens"] [text ")"]])
        infixTerms [] [] = []
        infixTerms str [] = [constant str]
        infixTerms ('_':str) (x:xs) = renderTerm' False ctx x : infixTerms str xs 
        infixTerms str args | (first, rest) <- span (/='_') str = constant first : infixTerms rest args

    freevar v = span_ [ class_ "freevar" ] (name v)
    metavar v r = span_ [ class_ "metavar" ] (name ('?':v) ++ r)
    constant v = span_ [ class_ "const" ] (name v)
    boundName txt = span_ [class_ "boundName"] (name txt)
    binder txt bdy = span_ [class_ "binder"] $ [boundName txt, text ".", space, bdy]

    renderITelescope ts = []

    peelApTelescope' t | (t', args) <- peelApTelescope t 
                       = case t' of 
                           MetaVar i | not (showTeles opts)
                                     -> let (args1, args2) = span isAtom args
                                         in (MetaVar i, args1, args2)
                           _ -> (t',[],args)
      where isAtom (LocalVar _) = True
            isAtom _ = False

renderRule = renderRuleName Nothing
renderRuleName = renderRuleNameE Nothing 
renderRuleNameE editable n ctx opts prp = case ruleStyle opts of 
          Turnstile -> (case n of (Just rr) -> div_ [] [renderRR' rr, text ":", space,renderProp (showInitialMetas opts) ctx [] prp ]
                                  Nothing   -> renderProp (showInitialMetas opts) ctx [] prp)
          s -> renderBigProp s ctx [] prp
  where
    metabinders pth vs = precontext 
                       $ (concat $ zipWith (metabinder' pth) [0..] vs)
                       ++ case editable of 
                            Just (idx, selected, n) -> case selected of 
                              ItemFocus idx' (I.RuleFocus (R.NewRuleBinderFocus pth')) 
                                   | idx == idx', pth == pth' -> [metabinderEditor Nothing (ItemAction (Just idx) (I.RuleAct (R.AddRuleBinder pth))) n]
                              ItemFocus idx' (I.RuleFocus (R.RuleTermFocus pth')) | idx' == idx, pth == pth' -> 
                                           [ button_ [class_ "addMB", onClick (SetFocus (ItemFocus idx (I.RuleFocus (R.NewRuleBinderFocus pth))))] [ span_ [class_ "typcn typcn-plus"] [] ]
                                           , span_ [class_ "metabinder"] [text "."] ]
                              _ -> []
                            _ -> []
        where precontext [] = span_ [] []
              precontext content = span_ [class_ "precontext"] content
    metabinder' pth i n = case editable of 
                            Just (idx, selected, n') -> case selected of
                              ItemFocus idx' (I.RuleFocus (R.RuleBinderFocus pth' i')) 
                                   | idx == idx', pth == pth', i == i' -> [metabinderEditor (Just (idx,pth,i)) (ItemAction (Just idx) $ I.RuleAct $ R.RenameRuleBinder pth i) n'] 
                              _ -> [ button_ [class_ "proofMB", onClick (SetFocus (ItemFocus idx (I.RuleFocus (R.RuleBinderFocus pth i)))) ] [ metabinder n ] ]
                            Nothing -> [ metabinder n ]
    metabinderEditor exists act n = form_ [ class_ "mbEditor", onSubmit act ]  $
                                     [ input_ [id_ "mbeditor", style_ (M.singleton "width" (pack (show $ (((fromIntegral (MS.length n) + 1) *16) / 30)) <> "em")) 
                                              , onInput (\s -> UpdateInput s), value_ n]
                                     , button_ [class_ "confirmButton" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     , script_ [] "document.getElementById('mbeditor').focus(); document.getElementById('mbeditor').select();"]
                                 ++ case exists of
                                     Just (idx,pth,i) -> [button_ [type_ "button", class_ "nix", onClick (ItemAction (Just idx) $ I.RuleAct $ R.DeleteRuleBinder pth i)] [span_ [class_ "typcn typcn-trash"] []] ]
                                     _ -> []
    renderTerm' ctx pth trm = case editable of 
                             Just (idx,selected, s) -> case selected of 
                                ItemFocus idx' (I.RuleFocus (R.RuleTermFocus pth')) | idx == idx', pth == pth' 
                                  -> span_ [] $ [termEditor idx ctx pth s]
                                            ++ if pth /= [] then [button_ [class_ "nix", onClick (ItemAction (Just idx) $ I.RuleAct $ R.DeletePremise pth)] [span_ [class_ "typcn typcn-trash"] []]]
                                                            else []
                                _ -> span_ [] [ button_ [class_ "ruleTB", onClick (SetFocus (ItemFocus idx (I.RuleFocus (R.RuleTermFocus pth))))] [renderTermCtx ctx (termDisplayOptions opts) trm]]
                             _ -> renderTermCtx ctx (termDisplayOptions opts) trm 

    termEditor i ctx pth n = form_ [ class_ "tmEditor", onSubmit (ItemAction (Just i) $ I.RuleAct $ R.UpdateTerm pth) ]  $
                             [ input_ [id_ "tmeditor", style_ (M.singleton "width" (pack (show $ (((fromIntegral (MS.length n) + 1) *16) / 30)) <> "em")) 
                                      , onInput (\s -> UpdateInput s), value_ n]
                             , button_ [class_ "confirmButton" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                             , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                             , script_ [] "document.getElementById('tmeditor').focus(); document.getElementById('tmeditor').select();"]

    context' pth v = case editable of 
                   Just (idx,selected,n) -> case selected of 
                      ItemFocus idx' (I.RuleFocus (R.RuleTermFocus pth')) | idx == idx', pth == pth' -> 
                            context (intersperse comma $ v ++ [button_ [class_ "addPremise", onClick $ ItemAction (Just idx) $ I.RuleAct $ R.AddPremise pth] [span_ [class_ "typcn typcn-plus-outline"] []]])
                      _ -> context (intersperse comma v)
                   _ -> context (intersperse comma v)

    isEditingMetas pth = case editable of 
       Just (idx,selected,n) -> case selected of 
          ItemFocus idx' (I.RuleFocus (R.RuleTermFocus pth')) | idx == idx', pth == pth' -> True
          ItemFocus idx' (I.RuleFocus (R.RuleBinderFocus pth' _)) | idx == idx', pth == pth' -> True
          ItemFocus idx' (I.RuleFocus (R.NewRuleBinderFocus pth')) | idx == idx', pth == pth' -> True
          _ -> False
       _ -> False
    isSelected pth = case editable of 
       Just (idx,selected,n) -> case selected of 
          ItemFocus idx' (I.RuleFocus (R.RuleTermFocus pth')) | idx == idx', pth == pth' -> Just idx
          _ -> Nothing
       _ -> Nothing

    renderRR' :: RuleRef -> View EditorAction
    renderRR' rr@(Local n) = renderRR rr
    renderRR' rr@(Defn n) = span_ [] $ case editable of 
                     Just (idx, selected,n) -> case selected of
                        ItemFocus idx' (I.RuleFocus R.NameFocus) | idx == idx' -> [ruleNameEditor idx n] 
                        _ -> [ button_ [class_ "ruleNameB", onClick (SetFocus $ ItemFocus idx $ I.RuleFocus R.NameFocus)] [ renderRR rr ] ]
                     Nothing -> [ renderRR rr ]

    ruleNameEditor idx n = form_ [ class_ "rnEditor", onSubmit (ItemAction (Just idx) $ I.RuleAct R.Rename) ] 
                                     [ input_ [id_ "rneditor", style_ (M.singleton "width" (pack (show $ (((fromIntegral (MS.length n) + 1) *16) / 30)) <> "em")) 
                                              , onInput (\s -> UpdateInput s), value_ n]
                                     , button_ [class_ "confirmButton" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     , script_ [] "document.getElementById('rneditor').focus(); document.getElementById('rneditor').select();"]


    renderProp metas ctx pth (Forall vs [] c) | not $ isEditingMetas pth = 
         span_ [class_ "prop"] $ (if metas then (metabinders pth vs :) else id) 
                               $ (if showEmptyTurnstile opts then (turnstile:) else id) 
                               $ [renderTerm' (reverse vs ++ ctx) pth c]
    renderProp metas ctx pth (Forall vs as c) = span_ [class_ "prop"] 
                                          $ (if metas then (metabinders pth vs:) else id)
                                              [ context' pth (zipWith (renderPropNested (reverse vs ++ ctx)) (map (:pth) [0..]) as)
                                              , turnstile, renderTerm' (reverse vs ++ ctx) pth c]

    renderPropNested ctx pth (Forall [] [] c) | not $ isEditingMetas pth = renderTerm' ctx pth c
    renderPropNested ctx pth p = span_ [] [text "(", renderProp True ctx pth p, text ")"]


    renderBigProp Dots ctx pth (Forall sks [] g) = renderProp True ctx pth (Forall sks [] g)
    renderBigProp style ctx pth (Forall sks lcls g) = 
        table_ [class_ "rulestep", intProp "cellpadding" 0, intProp "cellspacing" 0 ] $
          [ tr_ [class_ "premises"]
              (td_ [class_ "binderbox", rowspan_ $ if style == Dots then "3" else "2"] (if showInitialMetas opts || style == Dots then [metabinders pth sks] else [])
              : (map (td_ [class_ "premise"] . pure) (zipWith ((if  style == Bar then renderBigProp Dots else renderProp True) (reverse sks ++ ctx)) (map (:pth) [0..]) lcls)) 
              ++ [case isSelected pth of Nothing -> td_ [class_ "spacer"] [text ""] 
                                         Just idx -> td_ [class_ "spacer"] [button_ [class_ "addPremise", onClick (ItemAction (Just idx) $ I.RuleAct $ R.AddPremise pth) ] [span_ [class_ "typcn typcn-plus-outline"] []]] ]
              ++ [td_ [rowspan_ $ if style == Dots then "3" else "2", class_ "rulebox"] [maybe (text "") renderRR' (guard (style /= Dots) >> n)] ])]
          ++ (if style == Dots then [ tr_ [] [td_ [class_ "hypothetical", colspan_ (pack $ show $ length lcls + 1)] [text "⋮" ]]  ] else []) ++
          [ tr_ [] [td_ [class_ (if style /= Dots then "conclusion" else "hypconclusion"),colspan_ (pack $ show $ length lcls + 1)] 
                        [renderTerm' (reverse sks ++ ctx) pth g ]
                    ]
          ]


renderProofTree :: DisplayOptions -> Int -> ProofTree -> Maybe (R.Focus R.Rule, MisoString) -> View EditorAction
renderProofTree opts idx pt selected = renderPTStep [] [] [] pt
  where
    termDOs = tDOs opts
    ruleDOs = RDO { termDisplayOptions = termDOs , showEmptyTurnstile = False, showInitialMetas = True, ruleStyle = Turnstile }

    rulebinder v = span_ [ class_ "rulebinder" ] (localrule v : [sub_ [class_ "mini"] [text "⊢"]])
    
    renderPropNestedLabelled ctx i p = span_ [] [span_ [class_ "labelbracket"] [text "⟨"], renderRule ctx ruleDOs p, span_ [class_ "labelbracket"] [text "⟩"], sup_ [] [ localrule i ]]
    
    renderPTStep :: [Prop] -> [String] -> ProofTree.Path -> ProofTree -> View EditorAction
    renderPTStep rns ctx pth (PT sks lcls prp msgs) = 
        table_ [class_ "rulestep", intProp "cellpadding" 0, intProp "cellspacing" 0 ]
          [ tr_ [class_ "premises"]
              (td_ [class_ "binderbox", rowspan_ "2"] 
                     (   (if (showMetaBinders opts) then concat (zipWith (metabinder' pth) [0..] sks) else []) 
                      ++ (if (assumptionsMode opts == Hidden) then map rulebinder [length rns..length rns+length lcls - 1] else []))
              : (case msgs of 
                  Just (rr,sgs) -> map (td_ [class_ "premise"] . pure) (zipWith (renderPTStep (rns' ++ lcls) (reverse sks ++ ctx)) (map (:pth) [0..]) sgs) ++ [td_ [class_ "spacer"] [text ""]]
                  Nothing       ->  [td_ [class_ "spacer"] 
                          (goalButton pth )
                    ])
               ++ [td_ [rowspan_ "2", class_ "rulebox"] [maybe (text "?") (addNix . renderRR . fst) msgs] ]) 
          , tr_ [] [td_ [class_ "conclusion",colspan_ (pack $ show $ maybe 0 (length . snd) msgs + 1)] 
                  (case assumptionsMode opts of 
                     Hidden -> [renderTermCtx (reverse sks ++ ctx ) termDOs prp  ]
                     New    -> (if not (null lcls) then [context (intersperse comma $ zipWith (renderPropNestedLabelled (reverse sks ++ ctx)) [length rns..] lcls), turnstile]  else []) ++  [renderTermCtx (reverse sks ++ ctx ) termDOs prp  ]
                     Cumulative -> [context (intersperse comma $ zipWith (renderPropNestedLabelled (reverse sks ++ ctx)) [0..] (rns' ++ lcls)), turnstile, renderTermCtx (reverse sks ++ ctx) termDOs prp  ]
                  ) ]
          ]
      where
        addNix t = span_ [] [t, button_ [class_ "nix", onClick (ItemAction (Just idx) $ I.RuleAct $ R.Nix pth)] [span_ [class_ "typcn typcn-trash"] []] ]
        rns' = map (Prop.raise (length sks)) rns
        


    metabinder' pth i n = case selected of
                             Just (R.ProofBinderFocus pth' i', n) | pth == pth', i == i' -> [metabinderEditor pth i n] 
                             _ -> [ button_ [class_ "proofMB", onClick (SetFocus $ ItemFocus idx $ I.RuleFocus $ R.ProofBinderFocus pth i)] [ metabinder n ] ]
    metabinderEditor pth i n = form_ [ class_ "mbEditor", onSubmit (ItemAction (Just idx) $ I.RuleAct $ R.RenameProofBinder pth i) ] 
                                     [input_ [id_ "mbeditor", style_ (M.singleton "width" (pack (show $ (((fromIntegral (MS.length n) + 1) *16) / 30)) <> "em")) , onInput (\s -> UpdateInput s), value_ n]
                                     , button_ [class_ "confirmButton" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     , script_ [] "document.getElementById('mbeditor').focus(); document.getElementById('mbeditor').select();"]

    
    goalButton :: ProofTree.Path -> [View EditorAction]
    goalButton pth = if Just (R.GoalFocus pth) == fmap fst selected then 
                        [button_ [class_ "selectedGoal", id_ "selGoal", onClick (SetFocus $ ItemFocus idx $ I.RuleFocus $ R.GoalFocus pth) ] [span_ [class_ "typcn typcn-location"] [] ]
                        , script_ [] "document.getElementById('selGoal').focus();"]
                     else 
                        [button_ [class_ "goal", onClick (SetFocus $ ItemFocus idx $ I.RuleFocus $ R.GoalFocus pth) ] [span_ [class_ "typcn typcn-location-outline"] []]]

metabinder v = span_ [ class_ "metabinder" ] (name v ++ [text "."])
context [] = span_ [ ] []
context v = span_ [class_ "context" ] v
space = span_ [class_ "space" ] [text " "] 
turnstile = span_ [class_ "turnstile" ] [text "⊢"] 
comma = span_ [class_ "comma" ] [text ","] 
placeholder = span_ [class_ "placeholder" ] [text "␣"] 
localrule i = span_ [ class_ "localrule" ] [text (pack (show i))]
renderRR (Defn d) = span_ [ class_ "definedrule" ] (name d)
renderRR (Local i) = localrule i

name [] = []
name ('_':str) = placeholder : name str
name (' ':str) = name str
name str | (first, rest) <- span (`notElem` ("_ " :: [Char])) str = name' first ++ name rest

name' s = let noPrimes = dropWhileEnd (== '\'') s
              bulk = dropWhileEnd (isDigit) noPrimes
              rest = drop (length bulk) noPrimes
              bulk' = case bulk of 
                    "/\\" -> "∧"
                    "\\/" -> "∨"
                    "not" -> "¬"
                    "->"  -> "→"
                    "<-"  -> "←"
                    "<->" -> "↔"
                    "-->"  -> "⟶"
                    "<--"  -> "⟵ "
                    "<-->" -> "⟷"
                    "=>"  -> "⇒"
                    "<=="  -> "⇐"
                    "<=>" -> "⇔"
                    "<==>" -> "⟺"
                    "==>" -> "⟹"
                    "<===" -> "⟸"
                    "<-|"  -> "↤"
                    "=="   -> "≡"
                    "lub"  -> "⊓"
                    "glb"  -> "⊔"
                    "~="   -> "≃"
                    "~"    -> "∼"
                    "all"  -> "∀" 
                    "exists" -> "∃"
                    ":="   -> "≔"
                    "times"   -> "×"
                    "bot"   -> "⊥"
                    "top"   -> "⊤"
                    "infinity" -> "∞"
                    "[["  -> "〚"
                    "]]"  -> "〛"
                    "[<"  -> "〈"
                    ">]"  -> "〉"
                    ">>]"  -> "》"
                    "[<<"  -> "《"
                    "<="   -> "≤"
                    ">="   -> "≥"
                    "/="   -> "≠"
                    "|->" -> "↦"
                    "nat" -> "ℕ"
                    "rational" -> "ℚ"
                    "int" -> "ℤ"
                    "real" -> "ℝ"
                    "bool" -> "𝔹"
                    "product" -> "∏" 
                    "coproduct" -> "∐"  
                    "sum"       -> "∑"
                    "union" -> "∪"
                    "intersection" -> "∩"
                    "subseteq" -> "⊆"
                    "supseteq" -> "⊇"
                    "subset"   -> "⊂"
                    "supset"   -> "⊃"
                    "elem"     -> "∈"
                    "eval"     -> "⇓"
                    "alpha" -> "α"
                    "beta" -> "β"
                    "gamma" -> "γ"
                    "delta" -> "δ"
                    "epsilon" -> "ε"
                    "zeta" -> "ζ"
                    "eta" -> "η"
                    "theta" -> "θ"
                    "iota" -> "ι"
                    "kappa" -> "κ"
                    "lambda" -> "λ"
                    "varepsilon" -> "ϵ"
                    "mu" -> "μ"
                    "nu" -> "ν"
                    "xi" -> "ξ"
                    "pi" -> "π"
                    "rho" -> "ρ"
                    "sigma" -> "σ"
                    "varsigma" -> "ς"
                    "tau" -> "τ"
                    "phi" -> "φ"
                    "psi"-> "ψ"
                    "chi" -> "χ"
                    "omega" -> "ω"
                    "upsilon" -> "υ"
                    "Gamma" -> "Γ"
                    "Delta" -> "Δ"
                    "Theta" -> "Θ"
                    "Lambda" -> "Λ"
                    "Xi" -> "Ξ"
                    "Pi" -> "Π"
                    "Sigma" -> "Σ"
                    "Phi" -> "Φ"
                    "Psi"-> "Ψ"
                    "Omega" -> "Ω"
                    _ -> bulk
              primeString = makePrimeString (length s - length noPrimes)
              makePrimeString 0 = ""
              makePrimeString 1 = "′"
              makePrimeString 2 = "″"
              makePrimeString 3 = "‴"
              makePrimeString 4 = "⁗"
              makePrimeString n = "⁗" <> makePrimeString (n - 4)

           in if bulk' == "" then [text (pack rest)] else [text (pack bulk'), sub_ [] [text (pack rest)], text primeString ]             

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

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
import View.Term
import View.Utils
import View.Prop
import View.ProofTree
import View.Paragraph
import View.Heading
import View.Rule


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

updateModel :: EditorAction -> Editor -> Effect EditorAction Editor
updateModel act ed = noEff $ runAction act ed

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
                     in concatMap (renderPropGroup i p ctx) rs
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
        renderPropGroup i p ctx (n,rs) = div_ [class_ "insertItemHeader"] [text $ pack (n ++ ":")]:
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
 


renderScript textIn opts selected script = map (renderScriptItem textIn opts selected (length script)) (zip [0..] script)

renderScriptItem textIn opts selected scriptSize (i, item) = div_ [class_ $ if inserting then "itemBlock inserting" else "itemBlock"] $ [mainItem] ++ deleteButton:insertButton
  where
    mainItem = case item of 
      I.Paragraph para -> renderParagraph textIn selected i para
      I.Heading head -> renderHeading textIn selected i head
      I.Rule rule -> renderRule opts textIn selected i rule
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
                                     [ if isT then theoremHeading i else axiomHeading i
                                     , input_ [id_ "rneditor", style_ (M.singleton "width" (pack (show $ (((fromIntegral (MS.length textIn) + 1) *16) / 30)) <> "em")) 
                                              , onInput (\s -> UpdateInput s), value_ textIn]
                                     , button_ [class_ "confirmButton" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     , script_ [] "document.getElementById('rneditor').focus(); document.getElementById('rneditor').select();"]
                        _ -> []


renderAvailableRule ctx opts (i,p) (rr,r) 
     = button_ [class_ "ruleOption", onClick (ItemAction (Just i) $ I.RuleAct $ R.Apply (rr,r) p) ] [ renderPropName (Just rr) ctx ruleDOs r]
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




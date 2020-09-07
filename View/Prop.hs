{-# LANGUAGE OverloadedStrings #-}
module View.Prop where
import Terms
import ProofTree
import Editor 
import Prop
import View.Utils
import View.Term
import Miso hiding (on)
import Data.List (intersperse, dropWhileEnd, groupBy)
import Control.Monad
import qualified Miso.String as MS
import qualified Data.Map as M
import qualified Item as I
import qualified Rule as R

data RuleDisplayOptions = RDO { termDisplayOptions :: TermDisplayOptions, showInitialMetas :: Bool, ruleStyle :: RuleStyle, showEmptyTurnstile :: Bool } 

renderProp = renderPropName Nothing
renderPropName = renderPropNameE Nothing 
renderPropNameE editable n ctx opts prp = case ruleStyle opts of 
          Turnstile -> (case n of (Just rr) -> div_ [] [renderRR' rr, text ":", space,render (showInitialMetas opts) ctx [] prp ]
                                  Nothing   -> render (showInitialMetas opts) ctx [] prp)
          s -> renderBig s ctx [] prp
  where
    metabinders pth vs = precontext 
                       $ (concat $ zipWith (metabinder' pth) [0..] vs)
                       ++ case editable of 
                            Just (idx, selected, n) -> case selected of 
                              ItemFocus idx' (I.RuleFocus (R.NewRuleBinderFocus pth')) 
                                   | idx == idx', pth == pth' -> [metabinderEditor Nothing (ItemAction (Just idx) (I.RuleAct (R.AddRuleBinder pth))) n]
                              ItemFocus idx' (I.RuleFocus (R.RuleTermFocus pth')) | idx' == idx, pth == pth' -> 
                                           [ button_ [class_ "button-icon button-icon-blue button-icon-addbinder", onClick (SetFocus (ItemFocus idx (I.RuleFocus (R.NewRuleBinderFocus pth))))] [ typicon "plus" ]
                                           , span_ [class_ "metabinder"] [text "."] ]
                              _ -> []
                            _ -> []
        where precontext [] = span_ [] []
              precontext content = span_ [class_ "rule-binders"] content
    metabinder' pth i n = case editable of 
                            Just (idx, selected, n') -> case selected of
                              ItemFocus idx' (I.RuleFocus (R.RuleBinderFocus pth' i')) 
                                   | idx == idx', pth == pth', i == i' -> [metabinderEditor (Just (idx,pth,i)) (ItemAction (Just idx) $ I.RuleAct $ R.RenameRuleBinder pth i) n'] 
                              _ -> [ button_ [class_ "editable editable-math", onClick (SetFocus (ItemFocus idx (I.RuleFocus (R.RuleBinderFocus pth i)))) ] [ metabinder n ] ]
                            Nothing -> [ metabinder n ]
    metabinderEditor exists act n = form_ [ class_ "editor editor-expanding", onSubmit act ]  $
                                     [ input_ [id_ "mbeditor", style_ (M.singleton "width" (MS.pack (show $ (((fromIntegral (MS.length n) + 1) *16) / 30)) <> "em")) 
                                              , onInput (\s -> UpdateInput s), value_ n]
                                     , button_ [class_ "button-icon button-icon-blue" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "button-icon button-icon-grey", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     , script_ [] "document.getElementById('mbeditor').focus(); document.getElementById('mbeditor').select();"]
                                 ++ case exists of
                                     Just (idx,pth,i) -> [button_ [type_ "button", class_ "button-icon button-icon-red", onClick (ItemAction (Just idx) $ I.RuleAct $ R.DeleteRuleBinder pth i)] [span_ [class_ "typcn typcn-trash"] []] ]
                                     _ -> []
    renderTerm' ctx pth trm = case editable of 
                             Just (idx,selected, s) -> case selected of 
                                ItemFocus idx' (I.RuleFocus (R.RuleTermFocus pth')) | idx == idx', pth == pth' 
                                  -> span_ [] $ [termEditor idx ctx pth s]
                                            ++ if pth /= [] then [button_ [class_ "button-icon button-icon-red", onClick (ItemAction (Just idx) $ I.RuleAct $ R.DeletePremise pth)] [span_ [class_ "typcn typcn-trash"] []]]
                                                            else []
                                _ -> span_ [] [ button_ [class_ "editable editable-math", onClick (SetFocus (ItemFocus idx (I.RuleFocus (R.RuleTermFocus pth))))] [renderTermCtx ctx (termDisplayOptions opts) trm]]
                             _ -> renderTermCtx ctx (termDisplayOptions opts) trm 

    termEditor i ctx pth n = form_ [ class_ "editor editor-expanding", onSubmit (ItemAction (Just i) $ I.RuleAct $ R.UpdateTerm pth) ]  $
                             [ input_ [id_ "tmeditor", style_ (M.singleton "width" (MS.pack (show $ (((fromIntegral (MS.length n) + 1) *16) / 30)) <> "em")) 
                                      , onInput (\s -> UpdateInput s), value_ n]
                             , button_ [class_ "button-icon button-icon-blue" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                             , button_ [class_ "button-icon button-icon-grey", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                             , script_ [] "document.getElementById('tmeditor').focus(); document.getElementById('tmeditor').select();"]

    context' pth v = case editable of 
                   Just (idx,selected,n) -> case selected of 
                      ItemFocus idx' (I.RuleFocus (R.RuleTermFocus pth')) | idx == idx', pth == pth' -> 
                            context (intersperse comma $ v ++ [button_ [class_ "button-icon button-icon-blue button-icon-addpremise", onClick $ ItemAction (Just idx) $ I.RuleAct $ R.AddPremise pth] [span_ [class_ "typcn typcn-plus-outline"] []]])
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
                        _ -> [ button_ [class_ "editable editable-math", onClick (SetFocus $ ItemFocus idx $ I.RuleFocus R.NameFocus)] [ renderRR rr ] ]
                     Nothing -> [ renderRR rr ]

    ruleNameEditor idx n = form_ [ class_ "editor editor-expanding", onSubmit (ItemAction (Just idx) $ I.RuleAct R.Rename) ] 
                                     [ input_ [id_ "rneditor", style_ (M.singleton "width" (MS.pack (show $ (((fromIntegral (MS.length n) + 1) *16) / 30)) <> "em")) 
                                              , onInput (\s -> UpdateInput s), value_ n]
                                     , button_ [class_ "button-icon button-icon-blue" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "button-icon button-icon-grey", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     , script_ [] "document.getElementById('rneditor').focus(); document.getElementById('rneditor').select();"]


    render metas ctx pth (Forall vs [] c) | not $ isEditingMetas pth = 
         span_ [class_ "rule"] $ (if metas then (metabinders pth vs :) else id) 
                               $ (if showEmptyTurnstile opts then (turnstile:) else id) 
                               $ [renderTerm' (reverse vs ++ ctx) pth c]
    render metas ctx pth (Forall vs as c) = span_ [class_ "rule"] 
                                          $ (if metas then (metabinders pth vs:) else id)
                                              [ context' pth (zipWith (renderNested (reverse vs ++ ctx)) (map (:pth) [0..]) as)
                                              , turnstile, renderTerm' (reverse vs ++ ctx) pth c]

    renderNested ctx pth (Forall [] [] c) | not $ isEditingMetas pth = renderTerm' ctx pth c
    renderNested ctx pth p = span_ [] [text "(", render True ctx pth p, text ")"]


    renderBig Dots ctx pth (Forall sks [] g) = render True ctx pth (Forall sks [] g)
    renderBig style ctx pth (Forall sks lcls g) = 
        table_ [intProp "cellpadding" 0, intProp "cellspacing" 0 ] $
          [ tr_ []
              (td_ [class_ "rule-cell rule-binderbox", rowspan_ $ if style == Dots then "3" else "2"] (if showInitialMetas opts || style == Dots then [metabinders pth sks] else [])
              : (map (td_ [class_ "rule-cell rule-premise"] . pure) (zipWith ((if  style == Bar then renderBig Dots else render True) (reverse sks ++ ctx)) (map (:pth) [0..]) lcls)) 
              ++ [case isSelected pth of Nothing -> td_ [class_ "rule-cell rule-spacer"] [text ""] 
                                         Just idx -> td_ [class_ "rule-cell rule-spacer"] [button_ [class_ "button-icon button-icon-blue button-icon-addpremise", onClick (ItemAction (Just idx) $ I.RuleAct $ R.AddPremise pth) ] [span_ [class_ "typcn typcn-plus-outline"] []]] ]
              ++ [td_ [rowspan_ $ if style == Dots then "3" else "2", class_ "rule-cell rule-rulebox"] [maybe (text "") renderRR' (guard (style /= Dots) >> n)] ])]
          ++ (if style == Dots then [ tr_ [] [td_ [class_ "rule-cell", colspan_ (MS.pack $ show $ length lcls + 1)] [text "⋮" ]]  ] else []) ++
          [ tr_ [] [td_ [class_ (if style /= Dots then "rule-cell rule-conclusion" else "rule-cell rule-hypothetical-conclusion"),colspan_ (MS.pack $ show $ length lcls + 1)] 
                        [renderTerm' (reverse sks ++ ctx) pth g ]
                    ]
          ]


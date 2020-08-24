-- | Haskell language pragma
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- | Haskell module declaration
module Main where

-- | Miso framework import
import Miso hiding (on)
import Miso.String hiding (zipWith, map, Ap, intersperse, length, dropWhileEnd, drop, span, null, filter, zip, reverse, concat, splitAt, concatMap, all, groupBy)
import qualified Miso.String as MS
import Unification hiding (Masked (..))
import qualified Unification as U
import Prop 
import Script
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

  
data AssumptionsMode = Cumulative | New | Hidden
                     deriving (Show, Eq)
data DisplayOptions = O { showMetaBinders :: Bool, assumptionsMode :: AssumptionsMode, compactRules :: RuleStyle , tDOs :: TermDisplayOptions }
                    deriving (Show, Eq)
data TermDisplayOptions = TDO { showTeles :: Bool, showInfixes :: Bool } -- more later
                    deriving (Show, Eq)
data RuleStyle = BarTurnstile | Turnstile | Bar | Dots deriving (Show, Eq)

data RuleDisplayOptions = RDO { termDisplayOptions :: TermDisplayOptions, showInitialMetas :: Bool, ruleStyle :: RuleStyle, showEmptyTurnstile :: Bool } -- more later

-- | Type synonym for an application model
data Model = M { script :: [Item], displayOptions :: DisplayOptions, selected :: Maybe (Int, Focus), message :: Maybe String, disableUI :: Bool}
  deriving (Show, Eq)


data Focus = GoalFocus Path
           | ProofMetabinderFocus Path Int MisoString 
           | RuleMetabinderFocus Path Int MisoString 
           | RuleNameFocus MisoString 
           | RuleTermFocus Path MisoString
           | NewItemFocus
           | HeadingFocus MisoString
           | InsertingProposition Bool MisoString
           | BlockFocus MisoString
           | Credits
           deriving (Show, Eq)

-- | Sum type for application events
data Action = RunRule RuleRef (Int, Path) 
            | UnifierCompleted (Int, Path) (Either String Script)
            | Reset | ChangeDisplayOptions DisplayOptions | SelectGoal (Int, Path) | Nix (Int, Path)
            | Noop | ShowCredits
            | ShiftDown Int
            | SelectProofMetabinder Int Path Int String
            | RenameProofMetabinder Int Path Int
            | SelectRuleMetabinder Int Path Int String
            | SelectRuleNewMetabinder Int Path Int String
            | AddRuleMetabinder Int Path Int
            | RenameRuleMetabinder Int Path Int
            | DeleteRuleMetabinder Int Path Int
            | SelectRuleName Int String
            | SelectBlock Int MisoString
            | RenameRule Int
            | SelectRuleTerm Int Path String
            | AddPremise Int Path
            | DeletePremise Int Path
            | UpdateTerm Int Path
            | UpdateInput MisoString
            | DeleteItem Int
            | NewItemMenu Int
            | InsertHeading Int Int
            | InsertBlock Int
            | SelectHeading Int MisoString
            | UpdateHeading Int
            | UpdateBlock Int
            | InsertProposition Int Bool MisoString
            | ConfirmProposition Int
            deriving (Show, Eq)


-- | Entry point for a miso application
main :: IO ()
main = startApp App {..}
  where
    initialAction = Reset -- initial action to be executed on application load
    model  = initialModel         -- initial model
    update = updateModel          -- update function
    view   = viewModel            -- view function
    events = defaultEvents        -- default delegated events
    subs   = []                   -- empty subscription list
    mountPoint = Nothing          -- mount point for application (Nothing defaults to 'body')
    logLevel = Off                -- used during prerendering to see if the VDOM and DOM are in synch (only used with `miso` function)

-- | Updates model, optionally introduces side effects
updateModel :: Action -> Model -> Effect Action Model
updateModel (UnifierCompleted (i,p) result) m = noEff $
     case result of
       Left e -> m { message = Just e, disableUI = False }
       Right s' -> let m' = m { script = s', disableUI = False  }
                       m'' = if validSelection (i,0:p) (script m')
                             then m' { selected = Just (i,GoalFocus $ 0:p) } 
                             else case outstandingGoals' (fromJust (itemPS (s'!!i))) of
                                    [] -> m' { selected = Nothing }
                                    (p:_) -> m' { selected = Just (i, GoalFocus p) }
                    in m'' { message = Nothing }
updateModel (UpdateInput s) m = noEff $ case selected m of 
                                          Just (i,ProofMetabinderFocus p x _) ->  m { selected = Just (i, ProofMetabinderFocus p x s) }
                                          Just (i,RuleMetabinderFocus p x _) ->  m { selected = Just (i, RuleMetabinderFocus p x s) }
                                          Just (i,RuleTermFocus p _) ->  m { selected = Just (i, RuleTermFocus p s) }
                                          Just (i,InsertingProposition iT _) ->  m { selected = Just (i, InsertingProposition iT s) }
                                          Just (i,RuleNameFocus _) ->  m { selected = Just (i, RuleNameFocus s) }
                                          Just (i,HeadingFocus _) ->  m { selected = Just (i, HeadingFocus s) }
                                          Just (i,BlockFocus _) ->  m { selected = Just (i, BlockFocus s) }
                                          _ -> m
updateModel Noop m = noEff m
updateModel _ m | disableUI m = noEff m
updateModel Reset m = effectSub (m { selected = Nothing}) (\ _ -> consoleLog (pack $ show m)) 
updateModel (ChangeDisplayOptions o) m = noEff (m { displayOptions = o})
updateModel (SelectGoal p) m = noEff (m { selected = Just (fmap GoalFocus p), message = Nothing})
updateModel (ShowCredits) m = noEff (m { selected = Just (0, Credits), message = Nothing})
updateModel (SelectProofMetabinder i p x s) m = noEff (m { message=Nothing, selected = Just (i , ProofMetabinderFocus p x (pack s))})
updateModel (SelectRuleMetabinder i p x s) m = noEff (m {  message=Nothing,selected = Just (i , RuleMetabinderFocus p x (pack s))})
updateModel (SelectRuleNewMetabinder i p x s) m = updateModel (UpdateTerm i p) m >>= \m' ->
       noEff (m' {  message=Nothing,selected = Just (i , RuleMetabinderFocus p x (pack s))})
updateModel (SelectRuleName i s) m = noEff (m {  message=Nothing,selected = Just (i , RuleNameFocus (pack s))})
updateModel (SelectHeading i s) m = noEff (m {  message=Nothing,selected = Just (i , HeadingFocus s)})
updateModel (SelectBlock i s) m = noEff (m {  message=Nothing,selected = Just (i , BlockFocus s)})
updateModel (SelectRuleTerm i p s) m = noEff (m {  message=Nothing,selected = Just (i , RuleTermFocus p (pack s))})
updateModel (InsertProposition i isT s) m = noEff (m {  message=Nothing,selected = Just (i , InsertingProposition isT s)})
updateModel (NewItemMenu i) m = noEff (m {  message=Nothing,selected = Just (i , NewItemFocus)})
updateModel (UpdateTerm i p) m =  noEff $
   let s = unpack $ stringInput m
    in case updateRuleTerm s (i,p) (script m) of
          Left e -> m { message = Just e }
          Right script' -> let 
                 selected' = case p of [] -> Nothing
                                       (_:rest)  -> Just ( i, RuleTermFocus rest (pack (ruleString rest $ itemProp (script' !! i))))
              in m { selected = selected', message = Nothing, script = script' }
 where stringInput m = let Just (_, RuleTermFocus _ s) = selected m
                        in s
updateModel (ShiftDown i) m = clearFocus #>
    m { script = moveItemDown i (script m), message = Nothing, selected = Nothing }
  where
    clearFocus = do 
      blur $ "up" <> pack (show (i+1))
      blur $ "dn" <> pack (show i)
      pure Reset
updateModel (UpdateHeading i) m =  noEff $
   let s = stringInput m
    in m { script = modifyAt i (\(Heading l _) -> Heading l s) (script m), message = Nothing, selected = Nothing }
 where stringInput m = let Just (_, HeadingFocus s) = selected m
                        in s
updateModel (RenameProofMetabinder i p x) m = noEff $ 
   let s = unpack $ stringInput m
    in case renameProofMeta s (i,p,x) (script m) of
          Left e -> m { message = Just e }
          Right script' -> m { selected = Nothing, message = Nothing, script = script' }
 where stringInput m = let Just (_, ProofMetabinderFocus _ _ s) = selected m
                        in s
updateModel (RenameRuleMetabinder i p x) m = noEff $ 
   let s = unpack $ stringInput m
    in case renameRuleMeta s (i,p,x) (script m) of
          Left e -> m { message = Just e }
          Right script' -> m { selected = Nothing, message = Nothing, script = script' }
 where stringInput m = let Just (_, RuleMetabinderFocus _ _ s) = selected m
                        in s
updateModel (DeleteRuleMetabinder i p x) m = noEff $
       case deleteRuleMeta (i,p,x) (script m) of
          Left e -> m { message = Just e }
          Right script' -> m { selected = Nothing, message = Nothing, script = script' }
updateModel (AddRuleMetabinder i p x) m = noEff $
   let s = unpack $ stringInput m 
    in case addRuleMeta s (i,p,x) (script m) of 
         Left e -> m { message = Just e }
         Right script' -> m { selected = Just (i , RuleTermFocus p (pack (ruleString p $ itemProp (script' !! i)))), message = Nothing, script = script' }
 where stringInput m = let Just (_, RuleMetabinderFocus _ _ s) = selected m
                        in s
updateModel (RenameRule i) m = noEff $ 
   let s = unpack $ stringInput m
    in case renameRule s i (script m) of
          Left e -> m { message = Just e }
          Right script' -> m { message = Nothing, selected = Nothing, script = script' }
 where stringInput m = let Just (_, RuleNameFocus s) = selected m
                        in s
updateModel (ConfirmProposition i) m = noEff $ 
   let s' = unpack s
    in case insertProposition s' (i+1) isT (script m) of
          Left e -> m { message = Just e }
          Right script' -> m { message = Nothing, selected = Just (i+1, RuleTermFocus [] "???"), script = script' }
 where Just (_, InsertingProposition isT s) = selected m
updateModel (Nix (i,p)) m = noEff $ 
       m { selected = Just (i,GoalFocus p)
         , script = proofAction (nix p) i (script m)
         , message = Nothing
         }
updateModel (RunRule rr (i,p)) m = m { disableUI = True } <# do
           x <- timeout 2000000 $ evaluatePT i $ apply rr (i,p) (script m)
           case x of 
             Just v -> pure (UnifierCompleted (i,p) v)
             Nothing -> pure (UnifierCompleted (i,p) (Left "Cannot find unifier (timeout)"))
  where 
    evaluatePT i (Right s) | Proposition _ _ (Just (PS _ _ flx))  <- s !! i = do evaluate flx; pure (Right s)
    evaluatePT i (Left e ) = return (Left e)
 
updateModel (AddPremise i p) m = updateModel (UpdateTerm i p) m >>= \m'->
                                 let (s', pth) = addPremise i p $ script m'
                                   in noEff (m' { script = s', selected = Just (i, RuleTermFocus pth "???") })
updateModel (DeletePremise i p) m = noEff (m { selected = Nothing, script = deletePremise i p $ script m }) 
updateModel (DeleteItem i) m = noEff $ m { script = deleteItem i $ script m
                                         , selected = Nothing } 
updateModel (UpdateBlock i) m =  noEff $
   let s = stringInput m
    in m { script = modifyAtMany i (\(Block _) -> blocksFor s) (script m), message = Nothing, selected = Nothing }
 where stringInput m = let Just (_, BlockFocus s) = selected m
                        in s
       blocksFor = map Block .  map MS.unlines . filter (not . all MS.null) .  groupBy ((==) `on` MS.null) . MS.lines 
updateModel (InsertHeading i l) m = noEff $ m
   { script = let (first,rest) = splitAt (i+1) (script m)
               in first ++ Heading l "Heading" : rest
   , selected = Just (i+1, HeadingFocus "Heading")
   }    
updateModel (InsertBlock i) m = noEff $ m
   { script = let (first,rest) = splitAt (i+1) (script m)
               in first ++ Block "" : rest
   , selected = Just (i+1, BlockFocus "")
   }    



-- | Constructs a virtual DOM from a model
viewModel :: Model -> View Action
viewModel x = div_ [class_ "topdiv", onKeyDown (\(KeyCode kc) -> if kc == 27 then Reset else Noop ) ] $
      [ div_ [class_ "mainpanel", id_ "mainpanel"] $ renderScript (displayOptions x) (selected x) (script x)  ++ [div_ [class_ "endofcontent"] []]
      , div_ [class_ "sidebar", id_ "sidebar"] $ logo:
          (case message x of 
              Just m ->  (div_ [class_ "errorMessage"] [text (pack m)]:)
              Nothing -> id) (div_ [class_ "sidebarmain"] (
          (case selected x of 
             Just (i, GoalFocus p) -> 
                   (let (ctx, rs) = rules' (i,p) (script x)
                    in concatMap (renderRuleGroup i p ctx) rs)
                ++ let flxes = flexes i (script x)
                     in if S.null flxes then []
                        else div_ [class_ "insertItemHeader"] [text "Unsolved constraints:"]: (map (renderFlexes (tDOs $ displayOptions x)) (S.toList (flexes i (script x))))
             Just (i, NewItemFocus) -> newItemMenu i
             Just (i, BlockFocus s) -> editingHelp
             Just (i, Credits) -> div_ [class_ "insertItemHeader"] [text "Credits"]
                                : div_ [class_ "creditsText"] 
                                       [ text "Holbert is made by ", a_ [href_ "http://liamoc.net"] [text "Liam O'Connor"], text", a lecturer at the University of Edinburgh," 
                                       , text "using GHCJS and the Miso framework. Some icons are from the Typicons icon set by Stephen Hutchings."
                                       , text " It (will be) released under the BSD3 license."
                                       , text " Some code is based on work by Daniel Gratzer and Tobias Nipkow." 
                                       ]
                                : []
             _ -> [ div_ [class_ "insertItemHeader"] [text "Facts Summary:"],renderIndex (script x)]))
          :renderDisplayOptions (displayOptions x):[])
      , script_ [] "Split(['#mainpanel','#sidebar'],{ sizes: [70,30], minSize:200});"
      ]
  where 
        renderRuleGroup i p ctx (n,rs) = div_ [class_ "insertItemHeader"] [text $ pack (n ++ ":")]:
                [div_ [class_ "optionsGroup"] $ map (renderAvailableRule ctx (displayOptions x) (i,p)) rs]
        selectedGF x | Just (i, GoalFocus p) <- selected x = Just (i,p)
                     | otherwise = Nothing
        logo = div_ [class_ "logo", onClick ShowCredits ] [small_ [] ["click for credits"], text "Holbert 0.1"]
        newItemMenu i = -- div_ [] 
          [  div_ [class_ "insertItemHeader"] [text "Proof elements:"]
          , button_ [onClick (InsertProposition i False "Name"), class_ "insertItemOption" ] [div_ [class_ "axiomHeading"] ["Axiom."]]
          , button_ [onClick (InsertProposition i True  "Name"), class_ "insertItemOption" ] [div_ [class_ "theoremHeading"] ["Theorem."]]
          , div_ [class_ "insertItemHeader"] [text "Text elements:"]
          , button_ [onClick (InsertHeading i 1), class_ "insertItemOption" ] [h2_ [] ["Heading 1"]]
          , button_ [onClick (InsertHeading i 2), class_ "insertItemOption"] [h3_ [] ["Heading 2"]]
          , button_ [onClick (InsertHeading i 3), class_ "insertItemOption"] [h4_ [] ["Heading 3"]]
          , button_ [onClick (InsertHeading i 4), class_ "insertItemOption"] [h5_ [] ["Heading 4"]]
          , button_ [onClick (InsertBlock i), class_ "insertItemOption"] [div_ [class_ "parabutton"] ["Paragraph"]]
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
             , td_ [class_ "inlineMath"] $ pure $ renderTerm (TDO True True) (U.Ap (U.Ap (U.Const "_/\\_") (U.Const "A")) (U.Const "B"))
             ]
           , tr_ [] 
             [ td_ [class_ "lhs"] [code_ [] [text "$A B:_/\\_ A B$"] ]
             , td_ [class_ "inlineMath"] $ pure $ renderTerm (TDO True True) (U.Ap (U.Ap (U.Const "_/\\_") (U.FreeVar "A")) (U.FreeVar "B"))
             ]
           ] 
         ]

renderIndex (_:script) = ul_ [class_ "indexSummary"] $ renderIndex' (zip [1..] script)
  where
    renderIndex' ((i, Heading lvl hd):scr) 
           | (itms, rest) <- span (within lvl) scr 
           = li_ [] [b_ [] [a_ [href_ $ "#anchor" <> (pack $ show i)] [text hd]], ul_ [] $ renderIndex' itms ] : renderIndex' rest
    renderIndex' ((i, Proposition n _ mpt):scr) 
           = li_ [] [ a_ [href_ $ "#anchor" <> (pack $ show i)] [renderRR $ Defn n]
                    , case mpt of 
                         Just ps | outstandingGoals ps -> span_ [class_ "typcn typcn-warning outstandingGoalIndicator" ] []
                                 | otherwise  -> span_ [class_ "typcn typcn-input-checked noGoalIndicator" ] []
                         Nothing -> span_ [] []
                    ]:renderIndex' scr
    renderIndex' ((i, _):scr) = renderIndex' scr
    renderIndex' [] = []
    within n (_,Heading lvl hd) = lvl > n
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


renderScript opts selected script = map (renderScriptItem opts selected (length script)) (zip [0..] script)

renderScriptItem opts selected scriptSize (i, item) = div_ [class_ $ if inserting then "itemBlock inserting" else "itemBlock"] $ [mainItem] ++ deleteButton:insertButton
  where
    mainItem = case item of 
      Proposition name prop mpt ->
         div_ []
           $ (if isNothing mpt then axiomHeading else theoremHeading) 
           : renderRuleNameE (Just (i,selected)) (Just (Defn name)) [] ruleDOs prop 
           : case mpt of 
               Just ps ->  [proofHeading, 
                           div_ [class_ "proofBox"] [renderProofTree opts i (stateTree ps) (selected >>= \(j,path) -> guard (i == j) >> pure path)]]
               Nothing ->  []
      Block txt -> div_ [] $ (div_ [class_ "moreItemOptions"] $ 
                                case selected of 
                                  Just (i', BlockFocus n) | i == i' -> [
                                       button_ [class_ "confirmButton", onClick (UpdateBlock i) ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     ]
                                  _ -> [button_ [class_ "editButton", onClick (SelectBlock i txt)] [ span_ [class_ "typcn typcn-edit"] [] ]])
                           : (case selected of
                                Just (i', BlockFocus n) | i == i' -> 
                                     [ textarea_ [ id_ "ta", onInput UpdateInput, class_ "paragraph"]  [text n]
                                     , script_ [] "it = document.getElementById('ta'); var fn = function() {  it.style.height=''; it.style.height = it.scrollHeight+'px'; }; window.setTimeout(fn,100); it.addEventListener('input',fn); it.focus();it.setSelectionRange(it.value.length, it.value.length);"
                                     ]
                                _ -> [div_ [class_ "paragraph"]  $ renderParagraph txt] )
                           
      Heading l txt -> case selected of 
                          Just (i',HeadingFocus n) | i == i' -> 
                            anchor i [ form_ [ class_ ("headingEditor h" <> (pack $ show l)), onSubmit (UpdateHeading i) ]  $
                                     [ input_ [id_ "hdeditor", onInput (\s -> UpdateInput s), value_ n]
                                     , button_ [class_ "confirmButton" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     , script_ [] "document.getElementById('hdeditor').focus(); document.getElementById('hdeditor').select();"]]
                          _ -> button_ [ onClick (SelectHeading i txt), class_ "headingButton" ] 
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
    inserting = selected == Just (i, NewItemFocus)
    insertButton = let (cls,icn) = if inserting then ("insertButtonActive","typcn typcn-plus")
                                                else ("insertButton", "typcn typcn-plus-outline")
                   in button_ [class_ cls, onClick (NewItemMenu i)] [span_ [class_ icn] []]:
                      case selected of
                        Just (i',InsertingProposition isT n) | i == i' -> pure $
                               form_ [ class_ "newRnEditor", onSubmit (ConfirmProposition i) ] 
                                     [ if isT then theoremHeading else axiomHeading
                                     , input_ [id_ "rneditor", style_ (M.singleton "width" (pack (show $ (((fromIntegral (MS.length n) + 1) *16) / 30)) <> "em")) 
                                              , onInput (\s -> UpdateInput s), value_ n]
                                     , button_ [class_ "confirmButton" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     , script_ [] "document.getElementById('rneditor').focus(); document.getElementById('rneditor').select();"]
                        _ -> []
                      
                   
    

renderFlexes opts (x,y) = div_ [class_ "flexflex"] [ renderTerm opts x, equals, renderTerm opts y ]
  where equals = span_ [class_ "equals"] [text " = "]

renderAvailableRule ctx opts (i,p) (rr,r) 
     = button_ [class_ "ruleOption", onClick (RunRule rr (i,p)) ] [ renderRuleName (Just rr) ctx ruleDOs r]
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
    renderTerm' outer ctx (Lam (U.M v) t) = binder v (renderTerm' True (v:ctx) t)
    renderTerm' outer ctx other = renderTerm'' outer ctx other 

    renderTerm'' outer ctx t | Lam _ _ <- t = span_ [] $ parenthesise [renderTerm' False ctx t]
                             | (x, ts, []) <- peelApTelescope' t = case x of 
                                 FreeVar i -> freevar i
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
            isAtom (FreeVar _) = True
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
                            Just (idx, selected) -> case selected of 
                              Just (idx', RuleMetabinderFocus pth' i n) | idx == idx', pth == pth', i == length vs -> [metabinderEditor (AddRuleMetabinder idx pth i) n]
                              Just (idx', RuleTermFocus pth' _) | idx' == idx, pth == pth' -> 
                                           [ button_ [class_ "addMB", onClick (SelectRuleNewMetabinder idx pth (length vs) "")] [ span_ [class_ "typcn typcn-plus"] [] ]
                                           , span_ [class_ "metabinder"] [text "."] ]
                              _ -> []
                            _ -> []
        where precontext [] = span_ [] []
              precontext content = span_ [class_ "precontext"] content
    metabinder' pth i n = case editable of 
                            Just (idx, selected) -> case selected of
                              Just (idx',RuleMetabinderFocus pth' i' n) | idx == idx', pth == pth', i == i' -> [metabinderEditor (RenameRuleMetabinder idx pth i) n] 
                              _ -> [ button_ [class_ "proofMB", onClick (SelectRuleMetabinder idx pth i n)] [ metabinder n ] ]
                            Nothing -> [ metabinder n ]
    metabinderEditor act n = form_ [ class_ "mbEditor", onSubmit act ]  $
                                     [ input_ [id_ "mbeditor", style_ (M.singleton "width" (pack (show $ (((fromIntegral (MS.length n) + 1) *16) / 30)) <> "em")) 
                                              , onInput (\s -> UpdateInput s), value_ n]
                                     , button_ [class_ "confirmButton" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     , script_ [] "document.getElementById('mbeditor').focus(); document.getElementById('mbeditor').select();"]
                                 ++ case act of 
                                       RenameRuleMetabinder idx pth i -> [ button_ [type_ "button", class_ "nix", onClick (DeleteRuleMetabinder idx pth i)] [span_ [class_ "typcn typcn-trash"] []] ]
                                       _ -> []
    renderTerm' ctx pth trm = case editable of 
                             Just (idx,selected) -> case selected of 
                                Just (idx',RuleTermFocus pth' s) | idx == idx', pth == pth' 
                                  -> span_ [] $ [termEditor idx ctx pth s] -- [renderTermCtx ctx (termDisplayOptions opts) trm]
                                            ++ if pth /= [] then [ button_ [class_ "nix", onClick (DeletePremise idx pth)] [span_ [class_ "typcn typcn-trash"] []]  ]
                                                            else []
                                _ -> span_ [] [ button_ [class_ "ruleTB", onClick (SelectRuleTerm idx pth (toSexps ctx trm))] [renderTermCtx ctx (termDisplayOptions opts) trm]]
                             _ -> renderTermCtx ctx (termDisplayOptions opts) trm 

    termEditor i ctx pth n = form_ [ class_ "tmEditor", onSubmit (UpdateTerm i pth) ]  $
                             [ input_ [id_ "tmeditor", style_ (M.singleton "width" (pack (show $ (((fromIntegral (MS.length n) + 1) *16) / 30)) <> "em")) 
                                      , onInput (\s -> UpdateInput s), value_ n]
                             , button_ [class_ "confirmButton" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                             , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                             , script_ [] "document.getElementById('tmeditor').focus(); document.getElementById('tmeditor').select();"]

    context' pth v = case editable of 
                   Just (idx,selected) -> case selected of 
                      Just (idx',RuleTermFocus pth' s) | idx == idx', pth == pth' -> 
                            context (intersperse comma $ v ++ [button_ [class_ "addPremise", onClick (AddPremise idx pth) ] [span_ [class_ "typcn typcn-plus-outline"] []]])
                      _ -> context (intersperse comma v)
                   _ -> context (intersperse comma v)

    isEditingMetas pth = case editable of 
       Just (idx,selected) -> case selected of 
          Just (idx',RuleTermFocus pth' _) | idx == idx', pth == pth' -> True
          Just (idx',RuleMetabinderFocus pth' _ _) | idx == idx', pth == pth' -> True
          _ -> False
       _ -> False
    isSelected pth = case editable of 
       Just (idx,selected) -> case selected of 
          Just (idx',RuleTermFocus pth' _) | idx == idx', pth == pth' -> Just idx
          _ -> Nothing
       _ -> Nothing

    renderRR' :: RuleRef -> View Action
    renderRR' rr@(Local n) = renderRR rr
    renderRR' rr@(Defn n) = span_ [] $ case editable of 
                     Just (idx, selected) -> case selected of
                        Just (idx',RuleNameFocus n) | idx == idx' -> [ruleNameEditor idx n] 
                        _ -> [ button_ [class_ "ruleNameB", onClick (SelectRuleName idx n)] [ renderRR rr ] ]
                     Nothing -> [ renderRR rr ]

    ruleNameEditor idx n = form_ [ class_ "rnEditor", onSubmit (RenameRule idx) ] 
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
                                         Just idx -> td_ [class_ "spacer"] [button_ [class_ "addPremise", onClick (AddPremise idx pth) ] [span_ [class_ "typcn typcn-plus-outline"] []]] ]
              ++ [td_ [rowspan_ $ if style == Dots then "3" else "2", class_ "rulebox"] [maybe (text "") renderRR' (guard (style /= Dots) >> n)] ])]
          ++ (if style == Dots then [ tr_ [] [td_ [class_ "hypothetical", colspan_ (pack $ show $ length lcls + 1)] [text "⋮" ]]  ] else []) ++
          [ tr_ [] [td_ [class_ (if style /= Dots then "conclusion" else "hypconclusion"),colspan_ (pack $ show $ length lcls + 1)] 
                        [renderTerm' (reverse sks ++ ctx) pth g ]
                    ]
          ]


renderProofTree :: DisplayOptions -> Int -> ProofTree -> Maybe Focus -> View Action
renderProofTree opts idx pt selected = render' [] [] [] pt
  where
    termDOs = tDOs opts
    ruleDOs = RDO { termDisplayOptions = termDOs , showEmptyTurnstile = False, showInitialMetas = True, ruleStyle = Turnstile }

    rulebinder v = span_ [ class_ "rulebinder" ] (localrule v : [sub_ [class_ "mini"] [text "⊢"]])
    
    renderPropNestedLabelled ctx i p = span_ [] [span_ [class_ "labelbracket"] [text "⟨"], renderRule ctx ruleDOs p, span_ [class_ "labelbracket"] [text "⟩"], sup_ [] [ localrule i ]]
    
    
    
    
    renderPTStep :: [Prop] -> [String] -> Path -> [String] -> [Prop] -> Term -> Maybe (RuleRef, [ProofTree]) -> View Action
    renderPTStep rns ctx pth sks lcls prp msgs = 
        table_ [class_ "rulestep", intProp "cellpadding" 0, intProp "cellspacing" 0 ]
          [ tr_ [class_ "premises"]
              (td_ [class_ "binderbox", rowspan_ "2"] 
                     (   (if (showMetaBinders opts) then concat (zipWith (metabinder' pth) [0..] sks) else []) 
                      ++ (if (assumptionsMode opts == Hidden) then map rulebinder [length rns..length rns+length lcls - 1] else []))
              : (case msgs of 
                  Just (rr,sgs) -> map (td_ [class_ "premise"] . pure) (zipWith (render' (rns' ++ lcls) (reverse sks ++ ctx)) (map (:pth) [0..]) sgs) ++ [td_ [class_ "spacer"] [text ""]]
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
        addNix t = span_ [] [t, button_ [class_ "nix", onClick (Nix (idx, pth))] [span_ [class_ "typcn typcn-trash"] []] ]
        rns' = map (raiseProp 0 (length sks)) rns
        


    metabinder' pth i n = case selected of
                             Just (ProofMetabinderFocus pth' i' n) | pth == pth', i == i' -> [metabinderEditor pth i n] 
                             _ -> [ button_ [class_ "proofMB", onClick (SelectProofMetabinder idx pth i n)] [ metabinder n ] ]
    metabinderEditor pth i n = form_ [ class_ "mbEditor", onSubmit (RenameProofMetabinder idx pth i) ] 
                                     [input_ [id_ "mbeditor", style_ (M.singleton "width" (pack (show $ (((fromIntegral (MS.length n) + 1) *16) / 30)) <> "em")) , onInput (\s -> UpdateInput s), value_ n]
                                     , button_ [class_ "confirmButton" ] [ span_ [class_ "typcn typcn-tick-outline"] []]
                                     , button_ [class_ "cancelButton", type_ "button", onClick Reset ] [ span_ [class_ "typcn typcn-times-outline"] []]
                                     , script_ [] "document.getElementById('mbeditor').focus(); document.getElementById('mbeditor').select();"]

    
    goalButton :: Path -> [View Action]
    goalButton pth = if Just (GoalFocus pth) == selected then 
                        [button_ [class_ "selectedGoal", id_ "selGoal", onClick (SelectGoal (idx, pth)) ] [span_ [class_ "typcn typcn-location"] [] ]
                        , script_ [] "document.getElementById('selGoal').focus();"]
                     else 
                        [button_ [class_ "goal", onClick (SelectGoal (idx, pth)) ] [span_ [class_ "typcn typcn-location-outline"] []]]
    render' :: [Prop] -> [String] -> Path -> ProofTree -> View Action
    render' rns ctx pth (Goal sks lcls prp) = renderPTStep rns ctx pth sks lcls prp Nothing
    render' rns ctx pth (Rule rr sks lcls prp sgs) = renderPTStep rns ctx pth sks lcls prp (Just (rr,sgs))

metabinder v = span_ [ class_ "metabinder" ] (name v ++ [text "."])
context [] = span_ [ ] []
context v = span_ [class_ "context" ] v
space = span_ [class_ "space" ] [text " "] 
turnstile = span_ [class_ "turnstile" ] [text "⊢"] 
comma = span_ [class_ "comma" ] [text ","] 
placeholder = span_ [class_ "placeholder" ] [text "␣"] 
localrule :: Int -> View Action
localrule i = span_ [ class_ "localrule" ] [text (pack (show i))]

renderRR :: RuleRef -> View Action
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
         

initialModel = let 
    (t1, c) = runState (goal [] r1) 0
    (t2, c') = runState (goal [] r2) 0
 in model' -- M [Heading 0 "Holbert Playground", Block "Welcome to Holbert!", Proposition "ImpI" r0 Nothing, Proposition "ImpE" r0'''' Nothing, Proposition "ConjI" r0' Nothing, Proposition "ConjE1" r0'' Nothing, Proposition "ConjE2" r0''' Nothing,  Heading 1 "Proofs", Proposition "ConjComm" r1 (Just (PS t1 c S.empty)), Proposition "ConjAssoc" r2 (Just (PS t2 c' S.empty)), Block lipsum ] (O True Cumulative BarTurnstile (TDO True True) ) Nothing Nothing False 
   where 
     implies a b = Ap (Ap (Const "_->_") a) b
     conjunct a b = Ap (Ap (Const "_/\\_") a) b
     lipsum = "Lorem ipsum dolor sit amet, consectetur adipiscing elit, sed do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum"
     r0 = Forall ["A" , "B" ]
                     [ Forall [] [Forall [] [] (U.LocalVar 1)] (U.LocalVar 0)  ]
                     (U.Ap (U.Ap (U.Const "_->_") (U.LocalVar 1)) (U.LocalVar 0))
     r0' = Forall ["A","B"]
                      [ Forall [] [] (U.LocalVar 1) 
                      , Forall [] [] (U.LocalVar 0)]
                      (U.Ap (U.Ap (U.Const "_/\\_") (U.LocalVar 1)) (U.LocalVar 0))
     r0'' = Forall ["A","B"]
                      [ Forall [] [] (U.Ap (U.Ap (U.Const "_/\\_") (U.LocalVar 1)) (U.LocalVar 0))]
                      (U.LocalVar 1)
     r0''' = Forall ["A","B"]
                      [ Forall [] [] (U.Ap (U.Ap (U.Const "_/\\_") (U.LocalVar 1)) (U.LocalVar 0))]
                     (U.LocalVar 0)
     r0'''' = Forall ["A","B"] [ Forall [] [] (implies (U.LocalVar 1) (U.LocalVar 0))
                               , Forall [] [] (U.LocalVar 1) ] (U.LocalVar 0)
     r1 = Forall ["A" , "B"] [] (implies (conjunct (LocalVar 1) (LocalVar 0))  (conjunct (LocalVar 0) (LocalVar 1)))
     r2 = Forall ["A" , "B", "C"] [] (implies (conjunct (conjunct (LocalVar 2) (LocalVar 1)) (LocalVar 0))  (conjunct (LocalVar 2) (conjunct (LocalVar 1) (LocalVar 0))))
 
lam x p = Lam (U.M x) p
model'=M {script = [Heading 0 "Holbert Prototype Demo",Block "Welcome to this demo of the Holbert prototype. Holbert is the combination of an online notebook and theorem prover. It allows for preparation of interactive documents which include proof exercises in natural deduction. \n",Heading 3 "A Warning",Block "Holbert is *very much pre-alpha software*. It is inefficient, hacked together, and likely has bugs. At this point, I am *not* looking for bug reports or help with development (although I will be in future!). This is just for demonstration purposes to show what I have been working on.  \n",Heading 1 "Design Philosophy",Block "I designed Holbert to be an educational tool. Ultimately, I plan to convert the notes from the Programming Languages course I taught for many years into this tool. Previous attempts to integrate theorem provers with PL foundations education have been quite successful (see /Software Foundations/, /Concrete Semantics/), but I feel that the complexity of tools such as Coq and Isabelle mean that their respective courses become less about PL foundations in general and more about how to operate the theorem prover effectively. People using these PL foundations books to learn how to use their proof assistants rather than to learn PL foundations is evidence of this. \n",Block "In addition, conventional proof assistants are large pieces of software that can be complicated to install. By making Holbert run in the browser, students don't have to install anything, and can even use a tablet or other device to access work.\n",Block "Holbert is both a document preparation system and a proof assistant. This way, proof problems and sets of rules and exercises can be embedded right within educational notes. In future, I want to extend this system to support examinations and assessments as well.\n",Block "Holbert is based on /natural deduction/ and /higher order logic/. Because it doesn't have a type system, this means the logic it encodes is *unsound*. So it should not be used to verify production software or anywhere where the theorems it proves should be trusted. Normally, I would be very opposed to removing type systems from anything, however removing the type system from higher order logic simplifies its pedagogy, particularly when teaching a course about type systems. If I used a typed theorem prover, in order to teach about types, I would first have to teach about types, which is an annoying circularity.\n",Heading 1 "Propositional Logic",Block "To give an example of Holbert in action, lets define basic propositional logic. All terms are given in untyped lambda calculus. Terms applied to constants with underscores in them are rendered as infix operators. For example, ~if_then_else_fi A B C~ is rendered as $A B C:if_then_else_fi A B C$. Many common operators and symbols have their ASCII approximations replaced with unicode, and trailing numbers are rendered as subscripts.\n",Proposition {itemName = "/\\ I", itemProp = Forall ["A","B"] [Forall [] [] (LocalVar 1),Forall [] [] (LocalVar 0)] (Ap (Ap (Const "_/\\_") (LocalVar 1)) (LocalVar 0)), itemPS = Nothing},Proposition {itemName = "/\\ E1", itemProp = Forall ["A","B"] [Forall [] [] (Ap (Ap (Const "_/\\_") (LocalVar 1)) (LocalVar 0))] (LocalVar 1), itemPS = Nothing},Proposition {itemName = "/\\ E2", itemProp = Forall ["A","B"] [Forall [] [] (Ap (Ap (Const "_/\\_") (LocalVar 1)) (LocalVar 0))] (LocalVar 0), itemPS = Nothing},Block "The implication rules give an example of a hypothetical derivation (i.e. a rule with a rule as a premise):\n",Proposition {itemName = "-> I", itemProp = Forall ["A","B"] [Forall [] [Forall [] [] (LocalVar 1)] (LocalVar 0)] (Ap (Ap (Const "_->_") (LocalVar 1)) (LocalVar 0)), itemPS = Nothing},Proposition {itemName = "-> E", itemProp = Forall ["A","B"] [Forall [] [] (Ap (Ap (Const "_->_") (LocalVar 1)) (LocalVar 0)),Forall [] [] (LocalVar 1)] (LocalVar 0), itemPS = Nothing},Block "The \"Display Options\" in the bottom section of the sidebar provides a few options for rendering these rules. By default, we use the \"Hybrid\" mode which uses linear notation for premises and vertical notation for the main inference vinculum. Vertical notation is closer to Gentzen's original notation for natural deduction.\n",Block "The rules are editable. Click any part of the rule to edit it. To add premises, first click on the conclusion to which you want to add a premise. Similarly for meta-binders.\n",Block "/Note/: Altering rules will delete any part of a proof that makes use of the rule, to ensure that theorems remain in a consistent state. Be careful of this!\n",Block "To add new rules (or indeed any other element), click on a plus sign icon on the right hand side of the main content panel, then click \"Axiom\".\n",Heading 2 "Proofs",Block "Proofs are constructed \"backwards\", in the bottom-up fashion working from the conclusion. Clicking on a goal tag on the proof tree for a Theorem gives a list of all available facts. Click on any such fact to apply it as an introduction rule. Only pattern unification is used. In the future, I plan to allow \"unsolved constraint\" steps where unification problems can be delayed, which will give more flexibility in working with proofs. I also plan to allow the user to explicitly instantiate metavariables in future.\n",Block "The first proof here (commutativity of conjunction) is partially complete already, whereas associativity has not been started:\n",Proposition {itemName = "/\\ Comm", itemProp = Forall ["A","B"] [] (Ap (Ap (Const "_->_") (Ap (Ap (Const "_/\\_") (LocalVar 1)) (LocalVar 0))) (Ap (Ap (Const "_/\\_") (LocalVar 0)) (LocalVar 1))), itemPS = Just (PS {stateTree = Rule (Defn "-> I") ["A","B"] [] (Ap (Ap (Const "_->_") (Ap (Ap (Const "_/\\_") (LocalVar 1)) (LocalVar 0))) (Ap (Ap (Const "_/\\_") (LocalVar 0)) (LocalVar 1))) [Rule (Defn "/\\ I") [] [Forall [] [] (Ap (Ap (Const "_/\\_") (LocalVar 1)) (LocalVar 0))] (Ap (Ap (Const "_/\\_") (LocalVar 0)) (LocalVar 1)) [Rule (Defn "/\\ E2") [] [] (LocalVar 0) [Rule (Local 0) [] [] (Ap (Ap (Const "_/\\_") (LocalVar 1)) (LocalVar 0)) []],Rule (Defn "/\\ E1") [] [] (LocalVar 1) [Rule (Local 0) [] [] (Ap (Ap (Const "_/\\_") (LocalVar 1)) (LocalVar 0)) []]]], counter = 10, stateFlexes = fromList []})},Proposition {itemName = "/\\ Assoc", itemProp = Forall ["A","B","C"] [] (Ap (Ap (Const "_->_") (Ap (Ap (Const "_/\\_") (Ap (Ap (Const "_/\\_") (LocalVar 2)) (LocalVar 1))) (LocalVar 0))) (Ap (Ap (Const "_/\\_") (LocalVar 2)) (Ap (Ap (Const "_/\\_") (LocalVar 1)) (LocalVar 0)))), itemPS = Just (PS {stateTree = Goal ["A","B","C"] [] (Ap (Ap (Const "_->_") (Ap (Ap (Const "_/\\_") (Ap (Ap (Const "_/\\_") (LocalVar 2)) (LocalVar 1))) (LocalVar 0))) (Ap (Ap (Const "_/\\_") (LocalVar 2)) (Ap (Ap (Const "_/\\_") (LocalVar 1)) (LocalVar 0)))), counter = 0, stateFlexes = fromList []})},Heading 2 "Disjunction and Negation",Block "We haven't yet specified all the remaining bits of propositional logic, so let's quickly do that now:\n",Proposition {itemName = "\\/ I1", itemProp = Forall ["A","B"] [Forall [] [] (LocalVar 1)] (Ap (Ap (Const "_\\/_") (LocalVar 1)) (LocalVar 0)), itemPS = Nothing},Proposition {itemName = "\\/ I2", itemProp = Forall ["A","B"] [Forall [] [] (LocalVar 0)] (Ap (Ap (Const "_\\/_") (LocalVar 1)) (LocalVar 0)), itemPS = Nothing},Proposition {itemName = "\\/ E", itemProp = Forall ["A","B","C"] [Forall [] [] (Ap (Ap (Const "_\\/_") (LocalVar 2)) (LocalVar 1)),Forall [] [Forall [] [] (LocalVar 2)] (LocalVar 0),Forall [] [Forall [] [] (LocalVar 1)] (LocalVar 0)] (LocalVar 0), itemPS = Nothing},Block "We will specify negation $A: not A$ as merely equivalent to $A: _->_ A bot$, with the same introduction and elimination rules as implication:\n",Proposition {itemName = "not I", itemProp = Forall ["P"] [Forall [] [Forall [] [] (LocalVar 0)] (Const "bot")] (Ap (Const "not") (LocalVar 0)), itemPS = Nothing},Proposition {itemName = "not E", itemProp = Forall ["P"] [Forall [] [] (Ap (Const "not") (LocalVar 0)),Forall [] [] (LocalVar 0)] (Const "bot"), itemPS = Nothing},Block "Lastly, the rules to define the constants for true $top$ and false $bot$, where true has only an introduction rule and false has only an elimination rule.\n",Proposition {itemName = "top I", itemProp = Forall [] [] (Const "top"), itemPS = Nothing},Proposition {itemName = "bot E", itemProp = Forall ["P"] [Forall [] [] (Const "bot")] (LocalVar 0), itemPS = Nothing},Heading 3 "Constructivity",Block "The logic we have formalised so far is only constructive. We can prove only double negation introduction:\n",Proposition {itemName = "not not I", itemProp = Forall ["A"] [] (Ap (Ap (Const "_->_") (LocalVar 0)) (Ap (Const "not") (Ap (Const "not") (LocalVar 0)))), itemPS = Just (PS {stateTree = Rule (Defn "-> I") ["A"] [] (Ap (Ap (Const "_->_") (LocalVar 0)) (Ap (Const "not") (Ap (Const "not") (LocalVar 0)))) [Rule (Defn "not I") [] [Forall [] [] (LocalVar 0)] (Ap (Const "not") (Ap (Const "not") (LocalVar 0))) [Rule (Defn "not E") [] [Forall [] [] (Ap (Const "not") (LocalVar 0))] (Const "bot") [Rule (Local 1) [] [] (Ap (Const "not") (LocalVar 0)) [],Rule (Local 0) [] [] (LocalVar 0) []]]], counter = 4, stateFlexes = fromList []})},Block "To experiment with the above proof, you can press the trash can next to any rule application to reconstruct the proof from that point.\n",Proposition {itemName = "not not E", itemProp = Forall ["A"] [] (Ap (Ap (Const "_->_") (Ap (Const "not") (Ap (Const "not") (LocalVar 0)))) (LocalVar 0)), itemPS = Just (PS {stateTree = Goal ["A"] [] (Ap (Ap (Const "_->_") (Ap (Const "not") (Ap (Const "not") (LocalVar 0)))) (LocalVar 0)), counter = 0, stateFlexes = fromList []})},Block "The rules we have aren't enough to express this classical logic principle.\n",Heading 1 "Higher Order Abstract Syntax",Block "As Holbert terms are $lambda$ terms, we can use $lambda$-abstractions to encode variable binding structure, and avoid ugliness such as substitution. These $lambda$ abstractions are defined without much ceremony in Holbert, where $P: x. P x$ (written as ~x. P x~) is a $lambda$ term with a parameter $x$ and a result $P: P x$.\n",Proposition {itemName = "all I", itemProp = Forall ["P"] [Forall ["x"] [] (Ap (LocalVar 1) (LocalVar 0))] (Ap (Const "all") (lam "x" (Ap (LocalVar 1) (LocalVar 0)))), itemPS = Nothing},Proposition {itemName = "spec", itemProp = Forall ["P","x"] [Forall [] [] (Ap (Const "all") (lam "x" (Ap (LocalVar 2) (LocalVar 0))))] (Ap (LocalVar 1) (LocalVar 0)), itemPS = Nothing},Block "The above rule $spec$ might be considered an elimination rule for the $all$ quantifier, but the two metavariables in the one application do not play well with our unification algorithm (or indeed, any unification algorithm). Therefore, it's often more useful to have a slightly less direct elimination rule:\n",Proposition {itemName = "all E", itemProp = Forall ["R","P"] [Forall [] [] (Ap (Const "all") (lam "x" (Ap (LocalVar 1) (LocalVar 0)))),Forall [] [Forall ["x"] [] (Ap (LocalVar 1) (LocalVar 0))] (LocalVar 1)] (LocalVar 1), itemPS = Nothing},Block "The existential quantifier is the dual of the universal, and the rules are using a similar format:\n",Proposition {itemName = "exists I", itemProp = Forall ["P","x"] [Forall [] [] (Ap (LocalVar 1) (LocalVar 0))] (Ap (Const "exists") (lam "x" (Ap (LocalVar 2) (LocalVar 0)))), itemPS = Nothing},Proposition {itemName = "exists E", itemProp = Forall ["P","R"] [Forall [] [] (Ap (Const "exists") (lam "x" (Ap (LocalVar 2) (LocalVar 0)))),Forall ["x"] [Forall [] [] (Ap (LocalVar 2) (LocalVar 0))] (LocalVar 1)] (LocalVar 0), itemPS = Nothing},Block "As we are still in a constructive logic, we can prove only one direction of the classical equivalence between $P: exists (x. not (P x))$ and $P: not (all (x. P x))$.\n",Proposition {itemName = "exists not all", itemProp = Forall ["P"] [] (Ap (Ap (Const "_->_") (Ap (Const "exists") (lam "x" (Ap (Const "not") (Ap (LocalVar 1) (LocalVar 0)))))) (Ap (Const "not") (Ap (Const "all") (lam "x" (Ap (LocalVar 1) (LocalVar 0)))))), itemPS = Just (PS {stateTree = Rule (Defn "-> I") ["P"] [] (Ap (Ap (Const "_->_") (Ap (Const "exists") (lam "x" (Ap (Const "not") (Ap (LocalVar 1) (LocalVar 0)))))) (Ap (Const "not") (Ap (Const "all") (lam "x" (Ap (LocalVar 1) (LocalVar 0)))))) [Rule (Defn "exists E") [] [Forall [] [] (Ap (Const "exists") (lam "x" (Ap (Const "not") (Ap (LocalVar 1) (LocalVar 0)))))] (Ap (Const "not") (Ap (Const "all") (lam "x" (Ap (LocalVar 1) (LocalVar 0))))) [Rule (Local 0) [] [] (Ap (Const "exists") (lam "x" (Ap (Const "not") (Ap (LocalVar 1) (LocalVar 0))))) [],Rule (Defn "not I") ["x"] [Forall [] [] (Ap (Const "not") (Ap (LocalVar 1) (LocalVar 0)))] (Ap (Const "not") (Ap (Const "all") (lam "x" (Ap (LocalVar 2) (LocalVar 0))))) [Rule (Defn "not E") [] [Forall [] [] (Ap (Const "all") (lam "x" (Ap (LocalVar 2) (LocalVar 0))))] (Const "bot") [Rule (Local 1) [] [] (Ap (Const "not") (Ap (LocalVar 1) (LocalVar 0))) [],Rule (Defn "all E") [] [] (Ap (LocalVar 1) (LocalVar 0)) [Rule (Local 2) [] [] (Ap (Const "all") (lam "x" (Ap (LocalVar 2) (LocalVar 0)))) [],Rule (Local 3) [] [Forall ["x"] [] (Ap (LocalVar 2) (LocalVar 0))] (Ap (LocalVar 1) (LocalVar 0)) []]]]]], counter = 9, stateFlexes = fromList []})},Block "In the other direction, we do get almost to a complete proof, and at first glance it looks as though we could unify the metavariable with $x: x$ to complete the proof:\n",Proposition {itemName = "not all exists", itemProp = Forall ["P"] [] (Ap (Ap (Const "_->_") (Ap (Const "not") (Ap (Const "all") (lam "x" (Ap (LocalVar 1) (LocalVar 0)))))) (Ap (Const "exists") (lam "x" (Ap (Const "not") (Ap (LocalVar 1) (LocalVar 0)))))), itemPS = Just (PS {stateTree = Rule (Defn "-> I") ["P"] [] (Ap (Ap (Const "_->_") (Ap (Const "not") (Ap (Const "all") (lam "x" (Ap (LocalVar 1) (LocalVar 0)))))) (Ap (Const "exists") (lam "x" (Ap (Const "not") (Ap (LocalVar 1) (LocalVar 0)))))) [Rule (Defn "exists I") [] [Forall [] [] (Ap (Const "not") (Ap (Const "all") (lam "x" (Ap (LocalVar 1) (LocalVar 0)))))] (Ap (Const "exists") (lam "x" (Ap (Const "not") (Ap (LocalVar 1) (LocalVar 0))))) [Rule (Defn "not I") [] [] (Ap (Const "not") (Ap (LocalVar 0) (Ap (MetaVar "5") (LocalVar 0)))) [Rule (Defn "not E") [] [Forall [] [] (Ap (LocalVar 0) (Ap (MetaVar "5") (LocalVar 0)))] (Const "bot") [Rule (Local 0) [] [] (Ap (Const "not") (Ap (Const "all") (lam "x" (Ap (LocalVar 1) (LocalVar 0))))) [],Rule (Defn "all I") [] [] (Ap (Const "all") (lam "x" (Ap (LocalVar 1) (LocalVar 0)))) [Goal ["x"] [] (Ap (LocalVar 1) (LocalVar 0))]]]]], counter = 8, stateFlexes = fromList []})},Block "The reason this doesn't work becomes clearer if we show metavariable telescopes (the option in the sidebar). The variable $x: x$ does not occur in the telescope, and thus this metavariable cannot be unified with $x : x$.\n",Heading 1 "Future Plans",Block "In the short term, I will mostly be focused on making the codebase of Holbert fit to see the light of day. After that, the next features on the roadmap are:\n",Block "- User-supplied instantiation of metavariables.\n- Unsolved proof steps, where unification constraints can be delayed until later.\n- More text elements, such as code blocks and lists.\n- Saving and loading to local storage or to some server.\n",Block "More distantly, I plan to add:\n",Block "- Support for equality and definitions (can be encoded now but not nicely).\n- Rewriting//simplification by the above.\n- Equational reasoning proofs for preorders.\n",Block "Even more distantly, I will add:\n",Block "- Recursive functions\n- Generating induction principles and elimination rules.\n- Nicer (non-tree based) presentation of inductive // cases structure in proofs.\n- Support for locking parts of the sheet, for assessments and examinations\n"], displayOptions = O {showMetaBinders = True, assumptionsMode = New, compactRules = BarTurnstile, tDOs = TDO {showTeles = False, showInfixes = True}}, selected = Just (0,HeadingFocus "Holbert Prototype Demo"), message = Nothing, disableUI = False}


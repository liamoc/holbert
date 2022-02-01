{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Editor where
import Data.Maybe (fromJust, fromMaybe)
import qualified Miso.String as MS
import Optics.Core
import Control.Monad (foldM)
import Controller
import qualified Heading as H
import qualified Item as I
import qualified Paragraph as P
import qualified ProofTree as PT
import qualified Prop as Prp
import qualified Rule as R
import DisplayOptions

type Document = [I.Item]
type ItemIndex = Int

type InputText = MS.MisoString
type ErrorMessage = MS.MisoString

data Editor = Editor
  { document       :: Document
  , currentFocus   :: EditorFocus
  , inputText      :: InputText
  , message        :: Maybe ErrorMessage
  , displayOptions :: DisplayOptions
  } deriving (Show, Eq)

data EditorFocus
  = ItemFocus ItemIndex (Focus I.Item)
  | NoFocus
  | NewItemFocus ItemIndex
  | InsertingPropositionFocus Bool ItemIndex
  | CreditsFocus
  | ImportFocus
  deriving (Show, Eq)

data EditorAction
  = SetFocus EditorFocus
  | ItemAction (Maybe ItemIndex) (Action I.Item)
  | ChangeDisplayOptions DisplayOptions
  | Noop
  | Reset
  | ShiftDown ItemIndex
  | DeleteItem ItemIndex
  | NewItemMenu ItemIndex
  | UpdateInput MS.MisoString
  | InsertItem ItemIndex I.Item
  | InsertProposition ItemIndex Bool
  | Download
  | Import
  | LoadDocument Document
  | DisplayError MS.MisoString
  deriving (Show, Eq)

initialEditor :: Editor
initialEditor =
  Editor [I.Heading $ H.Heading 4 "Loading..."] NoFocus "index.holbert" Nothing (O True New BarTurnstile (TDO False True))

after :: Int -> AffineTraversal' [a] (a, [a])
after n = atraversalVL guts
  where
    guts :: AffineTraversalVL' [a] (a, [a])
    guts pure' act ls =
      let (lefts, itrights) = splitAt n ls
       in case itrights of
            (it : rights) ->
              (\(it', rights') -> lefts ++ it' : rights') <$> act (it, rights)
            _ -> pure' ls



getRuleAt :: Int -> Document -> R.Rule
getRuleAt i s = case s !! i of 
  I.Rule v -> v
  _ -> error "Rule not found!" 
rulesSummary :: (Int, PT.Path) -> Document -> ([MS.MisoString], [(MS.MisoString, [Prp.NamedProp])])
rulesSummary (i, p) s =
  let (lefts, I.Rule (R.R n prp (Just (R.PS pt c))) : rights) = splitAt i s
      context = fst $ fromJust $ ipreview (PT.path p PT.%+ PT.step) pt
      lcls = zip (map Prp.Local [0 ..]) (PT.locals context)
      ctx = PT.bound context
      rules = groupedRules lefts []
   in (ctx, filter (not . null . snd) (("Local Facts", lcls) : rules))
  where
    groupedRules :: Document -> [(MS.MisoString, [Prp.NamedProp])] -> [(MS.MisoString, [Prp.NamedProp])]
    groupedRules [] acc = acc
    groupedRules (I.Heading (H.Heading n str) : xs) acc
      | n < 2 = groupedRules xs ((str, []) : acc)
      | otherwise = groupedRules xs acc
    groupedRules (i : xs) (h : acc) =
      let rs = map (\(R.R n prp _) -> (Prp.Defn n, prp)) (toListOf I.rule i)
       in groupedRules xs (fmap (rs ++) h : acc)
    groupedRules (i : xs) [] = error "Script didn't start with a heading"

processRenames :: [(MS.MisoString, MS.MisoString)] -> Document -> Either MS.MisoString Document
processRenames rns doc = foldM processRename doc rns
  where
    names = concatMap defined doc
    processRename doc (s, s')
      | s' `elem` names = Left "Cannot rename: Name already in use"
      | otherwise = Right $ map (renamed (s, s')) doc

switchFocus :: EditorFocus -> Editor -> Editor
switchFocus (ItemFocus idx f) ed =
  let (lefts, x : rest) = splitAt idx (document ed)
  in ed
  { currentFocus = ItemFocus idx f
  , inputText = fromMaybe "" (editable (concatMap definedSyntax lefts) f x)
  }
switchFocus f ed = ed {currentFocus = f, inputText = ""}

runAction :: EditorAction -> Editor -> Editor
runAction act ed = case runAction' act ed of
  Left e -> ed {message = Just e}
  Right ed' -> ed'

runAction' :: EditorAction -> Editor -> Either MS.MisoString Editor
runAction' Noop ed = pure ed
runAction' Reset ed = pure (ed {message = Nothing, currentFocus = NoFocus})
runAction' (ItemAction mi act) ed = do
  let index | Just i <- mi = i
            | ItemFocus i _ <- currentFocus ed = i
  let (lefts,it:rights) = splitAt index (document ed)
  (item, mf, inv, rns) <- runController (handle act it) (inputText ed) (concatMap definedSyntax lefts)
  doc' <- processRenames rns (document ed)
  let doc'' = over (after index) (\(_, rest) -> (item, map (foldr (.) id (map invalidated inv)) rest)) doc'
      ed'   = ed {message = Nothing, document = doc''}
      (leave, newFocus) = case mf of
        Nothing -> (False, NoFocus)
        Just (leave, f) -> (leave, ItemFocus index f)
  (if leave then runAction' (SetFocus newFocus) else (pure . switchFocus newFocus)) ed'
runAction' (SetFocus f) ed = case currentFocus ed of
  ItemFocus i f' -> do
    let (lefts,it:rights) = splitAt i (document ed)
    (item, _, inv, rns) <- runController (leaveFocus f' it) (inputText ed) (concatMap definedSyntax lefts)
    let doc = over (after i) (\(_, rest) -> (item, map (foldr (.) id (map invalidated inv)) rest)) (document ed)
    Right $ switchFocus f (ed {message = Nothing, document = doc})
  _ -> Right $ switchFocus f (ed {message = Nothing})

runAction' (ChangeDisplayOptions opts) ed = pure (ed {displayOptions = opts})
runAction' (UpdateInput s) ed = pure (ed {inputText = s})

runAction' (InsertItem idx itm) ed =
  let (first, last) = splitAt (idx + 1) (document ed)
   in pure $ switchFocus (ItemFocus (idx + 1) $ inserted itm) $ ed
        { document = first ++ itm : last, message = Nothing }

runAction' (ShiftDown idx) ed =
  let (lefts, x : y : rest) = splitAt idx (document ed)
      y' = foldr (.) id (map invalidated (defined x)) y
   in pure (ed {document = lefts ++ y' : x : rest, currentFocus = NoFocus, message = Nothing})

runAction' (DeleteItem idx) ed =
  let (lefts, x : rest) = splitAt idx (document ed)
      rest' = map (foldr (.) id (map invalidated (defined x))) rest
   in pure (ed {document = lefts ++ rest', currentFocus = NoFocus, message = Nothing})

runAction' (InsertProposition idx b) ed =
  let n = inputText ed
      item = (if b then R.blankTheorem else R.blankAxiom) n
   in case n of
        "" -> Left "Name cannot be empty"
        _ | n `elem` concatMap defined (document ed) -> Left "Name already in use"
        _ -> runAction' (InsertItem idx (I.Rule item)) ed

runAction' (LoadDocument m) ed = Right $ ed { document = m, currentFocus = NoFocus, message = Nothing}
runAction' (DisplayError e) ed = Left e

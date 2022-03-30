{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Editor where
import Data.Maybe (fromJust, fromMaybe,mapMaybe)
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
import Debug.Trace

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
  | InsertingPropositionFocus R.RuleType ItemIndex
  | InductionFocus ItemIndex
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
  | InsertProposition ItemIndex R.RuleType
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
  
processNewnames :: [MS.MisoString] -> Document -> Either MS.MisoString ()
processNewnames nn doc = mapM_ processNewname nn
  where
    processNewname n = case n of
        "" -> Left "Name cannot be empty"
        _ | n `elem` concatMap (mapMaybe (Prp.defnName . fst) . defined) doc -> Left "Name already in use"
          | otherwise -> Right ()

processRenames :: [(MS.MisoString, MS.MisoString)] -> Document -> Either MS.MisoString Document
processRenames rns doc = foldM processRename doc rns
  where
    names = mapMaybe (Prp.defnName . fst) $ concatMap defined doc
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
  let localFocus = case currentFocus ed of 
       ItemFocus i' f | i' == index -> Just f
       _ -> Nothing
  let (lefts,it:rights) = splitAt index (document ed)
  (item, mf, inv, rns, nn) <- runController (handle act it) (inputText ed) (concatMap definedSyntax lefts) (concatMap defined lefts) localFocus
  processNewnames nn (document ed)
  doc' <- processRenames rns (document ed)
  let doc'' = over (after index) (\(_, rest) -> (item, map (foldr (.) id (map invalidated inv)) rest)) doc'
      ed'   = ed {message = Nothing, document = doc''}
      (leave, newFocus) = case mf of
        Clear -> (False, NoFocus)
        Switch f -> (False, ItemFocus index f)
        Leave f -> (True, ItemFocus index f)
  (if leave then runAction' (SetFocus newFocus) else (pure . switchFocus newFocus)) ed'
runAction' (SetFocus f) ed = case currentFocus ed of
  ItemFocus i f' -> do
    let (lefts,it:rights) = splitAt i (document ed)
    (item, _, inv, rns, nn) <- runController (leaveFocus f' it) (inputText ed) (concatMap definedSyntax lefts) (concatMap defined lefts) (Just ())
    processNewnames nn (document ed)
    doc' <- processRenames rns (document ed)
    let doc = over (after i) (\(_, rest) -> (item, map (foldr (.) id (map invalidated inv)) rest)) doc'
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
      y' = foldr (.) id (map (maybe id invalidated . Prp.defnName . fst) (defined x)) y
   in pure (ed {document = lefts ++ y' : x : rest, currentFocus = NoFocus, message = Nothing})

runAction' (DeleteItem idx) ed =
  let (lefts, x : rest) = splitAt idx (document ed)
      rest' = map (foldr (.) id (map (maybe id invalidated . Prp.defnName . fst) (defined x))) rest
   in pure (ed {document = lefts ++ rest', currentFocus = NoFocus, message = Nothing})

runAction' (InsertProposition idx ruleType) ed =
  let n = inputText ed
      item = (if ruleType == R.Theorem then R.blankTheorem
              else R.blankAxiom) ruleType n
   in case n of
        "" -> Left "Name cannot be empty"
        _ | n `elem` concatMap (mapMaybe (Prp.defnName . fst) . defined) (document ed) -> Left "Name already in use"
        _ -> runAction' (InsertItem idx (I.Rule item)) ed

runAction' (LoadDocument m) ed = Right $ ed { document = m, currentFocus = NoFocus, message = Nothing}
runAction' (DisplayError e) ed = Left e

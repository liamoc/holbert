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

type Document = [I.Item]
type ItemIndex = Int

type InputText = MS.MisoString
type ErrorMessage = MS.MisoString

data DisplayOptions = O 
  { showMetaBinders :: Bool
  , assumptionsMode :: AssumptionsMode
  , compactRules    :: RuleStyle
  , tDOs            :: TermDisplayOptions
  } deriving (Show, Eq)

data TermDisplayOptions = TDO {showTeles :: Bool, showInfixes :: Bool}
  deriving (Show, Eq)

data RuleStyle = BarTurnstile | Turnstile | Bar | Dots 
  deriving (Show, Eq)

data AssumptionsMode = Cumulative | New | Hidden
  deriving (Show, Eq)

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
  deriving (Show, Eq)

initialEditor :: Editor
initialEditor =
  Editor [I.Heading $ H.Heading 0 "Holbert Playground"] NoFocus "" Nothing (O True Cumulative BarTurnstile (TDO True True))

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

rulesSummary :: (Int, PT.Path) -> Document -> ([String], [(String, [Prp.NamedProp])])
rulesSummary (i, p) s =
  let (lefts, I.Rule (R.R n prp (Just (R.PS pt c))) : rights) = splitAt i s
      context = fst $ fromJust $ ipreview (PT.path p PT.%+ PT.step) pt
      lcls = zip (map Prp.Local [0 ..]) (PT.locals context)
      ctx = PT.bound context
      rules = groupedRules lefts []
   in (ctx, filter (not . null . snd) (("Local Facts", lcls) : rules))
  where
    groupedRules :: Document -> [(String, [Prp.NamedProp])] -> [(String, [Prp.NamedProp])]
    groupedRules [] acc = acc
    groupedRules (I.Heading (H.Heading n str) : xs) acc
      | n < 2 = groupedRules xs ((MS.unpack $ str, []) : acc)
      | otherwise = groupedRules xs acc
    groupedRules (i : xs) (h : acc) =
      let rs = map (\(R.R n prp _) -> (Prp.Defn n, prp)) (toListOf I.rule i)
       in groupedRules xs (fmap (rs ++) h : acc)
    groupedRules (i : xs) [] = error "Script didn't start with a heading"

processRenames :: [(String, String)] -> Document -> Either String Document
processRenames rns doc = foldM processRename doc rns
  where
    names = concatMap defined doc
    processRename doc (s, s')
      | s' `elem` names = Left "Cannot rename: Name already in use"
      | otherwise = Right $ map (renamed (s, s')) doc

switchFocus :: EditorFocus -> Editor -> Editor
switchFocus (ItemFocus idx f) ed = ed
  { currentFocus = ItemFocus idx f
  , inputText = fromMaybe "" (editable f (document ed !! idx))
  }
switchFocus f ed = ed {currentFocus = f, inputText = ""}

runAction :: EditorAction -> Editor -> Editor
runAction act ed = case runAction' act ed of
  Left e -> ed {message = Just $ MS.pack e}
  Right ed' -> ed'

runAction' :: EditorAction -> Editor -> Either String Editor
runAction' Noop ed = pure ed
runAction' Reset ed = pure (ed {message = Nothing, currentFocus = NoFocus})
runAction' (ItemAction mi act) ed = do
  let index | Just i <- mi = i
            | ItemFocus i _ <- currentFocus ed = i
  (item, mf, inv, rns) <- runController (handle act (document ed !! index)) (inputText ed)
  doc' <- processRenames rns (document ed)
  let doc'' = over (after index) (\(_, rest) -> (item, map (foldr (.) id (map invalidated inv)) rest)) doc'
      ed'   = ed {message = Nothing, document = doc''}
      (leave, newFocus) = case mf of
        Nothing -> (False, NoFocus)
        Just (leave, f) -> (leave, ItemFocus index f)
  (if leave then runAction' (SetFocus newFocus) else (pure . switchFocus newFocus)) ed'

runAction' (SetFocus f) ed = case currentFocus ed of
  ItemFocus i f' -> do
    (item, _, inv, rns) <- runController (leaveFocus f' (document ed !! i)) (inputText ed)
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
  let n = MS.unpack $ inputText ed
      item = (if b then R.blankTheorem else R.blankAxiom) n
   in case n of
        "" -> Left "Name cannot be empty"
        _ | n `elem` concatMap defined (document ed) -> Left "Name already in use"
        _ -> runAction' (InsertItem idx (I.Rule item)) ed
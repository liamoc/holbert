{-# LANGUAGE TypeFamilies #-}
module Controller where
import Control.Monad.Except
import Control.Monad.State
import qualified Miso.String as MS

data ControllerState focus = CS
  { toSetFocus :: Maybe (Bool, focus)
  , editing :: MS.MisoString
  , invalidates :: [String]
  , renames :: [(String, String)]
  }

type Controller focus a = ExceptT String (State (ControllerState focus)) a

runController :: Controller focus a -> MS.MisoString -> Either String (a, Maybe (Bool, focus), [String], [(String, String)])
runController act ed = case runState (runExceptT act) (CS Nothing ed [] []) of
  (Right a, CS f e iv rn) -> Right (a, f, iv, rn)
  (Left e, _) -> Left e

errorMessage :: String -> Controller focus a
errorMessage str = throwError str

clearFocus :: Controller focus ()
clearFocus = modify (\(CS ff txt inv rn) -> CS Nothing txt inv rn)

setFocusWithLeaving :: focus -> Controller focus ()
setFocusWithLeaving f = modify (\(CS ff txt inv rn) -> CS (Just (True, f)) txt inv rn)

setFocus :: focus -> Controller focus ()
setFocus f = modify (\(CS ff txt inv rn) -> CS (Just (False, f)) txt inv rn)

textInput :: Controller focus String
textInput = MS.unpack . editing <$> get

invalidate :: String -> Controller focus ()
invalidate n = modify (\(CS ff txt inv rn) -> (CS ff txt (n : inv) rn))

renameResource :: String -> String -> Controller focus ()
renameResource n m = modify (\(CS ff txt inv rn) -> (CS ff txt inv ((n, m) : rn)))

zoomFocus :: (focus -> focus') -> Controller focus a -> Controller focus' a
zoomFocus f act = do
  CS sf ed inv rn <- get
  case runState (runExceptT act) (CS Nothing ed inv rn) of
    (Left e, _) -> errorMessage e
    (Right a, (CS sf' ed' inv' rn')) -> put (CS (fmap f <$> sf') ed' inv' rn') >> pure a

noFocus :: Controller focus a -> Controller () a
noFocus = zoomFocus (const ())

class Control s where
  data Action s
  data Focus s
  handle :: Action s -> s -> Controller (Focus s) s
  leaveFocus :: Focus s -> s -> Controller () s
  editable :: Focus s -> s -> Maybe MS.MisoString
  invalidated :: String -> s -> s
  invalidated = const id
  renamed :: (String, String) -> s -> s
  renamed = const id
  defined :: s -> [String]
  defined = const []
  inserted :: s -> Focus s
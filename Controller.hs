{-# LANGUAGE TypeFamilies #-}
module Controller where
import Control.Monad.Except
import Control.Monad.State
import qualified Miso.String as MS
import StringRep (SyntaxTable)
data ControllerState focus = CS
  { toSetFocus :: Maybe (Bool, focus)
  , editing :: MS.MisoString
  , syntaxes :: SyntaxTable
  , invalidates :: [MS.MisoString]
  , renames :: [(MS.MisoString, MS.MisoString)]
  }

type Controller focus a = ExceptT MS.MisoString (State (ControllerState focus)) a

runController :: Controller focus a -> MS.MisoString -> SyntaxTable
              -> Either MS.MisoString (a, Maybe (Bool, focus), [MS.MisoString], [(MS.MisoString, MS.MisoString)])
runController act ed tbl = case runState (runExceptT act) (CS Nothing ed tbl [] []) of
  (Right a, CS f _ _ iv rn) -> Right (a, f, iv, rn)
  (Left e, _) -> Left e

errorMessage :: MS.MisoString -> Controller focus a
errorMessage str = throwError str

clearFocus :: Controller focus ()
clearFocus = modify (\(CS ff txt sy inv rn) -> CS Nothing txt sy inv rn)

setFocusWithLeaving :: focus -> Controller focus ()
setFocusWithLeaving f = modify (\(CS ff txt sy inv rn) -> CS (Just (True, f)) txt sy inv rn)

setFocus :: focus -> Controller focus ()
setFocus f = modify (\(CS ff txt sy inv rn) -> CS (Just (False, f)) txt sy inv rn)

textInput :: Controller focus MS.MisoString
textInput = editing <$> get

syntaxTable :: Controller focus SyntaxTable
syntaxTable = syntaxes <$> get

invalidate :: MS.MisoString -> Controller focus ()
invalidate n = modify (\(CS ff txt sy inv rn) -> (CS ff txt sy (n : inv) rn))

renameResource :: MS.MisoString -> MS.MisoString -> Controller focus ()
renameResource n m = modify (\(CS ff txt sy inv rn) -> (CS ff txt sy inv ((n, m) : rn)))

zoomFocus :: (focus -> focus') -> Controller focus a -> Controller focus' a
zoomFocus f act = do
  CS sf ed sy inv rn <- get
  case runState (runExceptT act) (CS Nothing ed sy inv rn) of
    (Left e, _) -> errorMessage e
    (Right a, (CS sf' ed' sy' inv' rn')) -> put (CS (fmap f <$> sf') ed' sy' inv' rn') >> pure a

noFocus :: Controller focus a -> Controller () a
noFocus = zoomFocus (const ())

class Control s where
  data Action s
  data Focus s
  handle :: Action s -> s -> Controller (Focus s) s
  leaveFocus :: Focus s -> s -> Controller () s
  editable :: SyntaxTable -> Focus s -> s -> Maybe MS.MisoString
  invalidated :: MS.MisoString -> s -> s
  invalidated = const id
  renamed :: (MS.MisoString, MS.MisoString) -> s -> s
  renamed = const id
  defined :: s -> [MS.MisoString]
  defined = const []  
  inserted :: s -> Focus s
  definedSyntax :: s -> SyntaxTable
  definedSyntax = const []  
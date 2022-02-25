{-# LANGUAGE TypeFamilies, DeriveFunctor #-}
module Controller where
import Control.Monad.Except
import Control.Monad.State
import qualified Prop as P
import qualified Miso.String as MS
import StringRep (SyntaxTable)

data FocusOutcome focus = Switch focus | Leave focus | Clear deriving (Functor)

data ControllerState focus = CS
  { toSetFocus :: FocusOutcome focus
  , editing :: MS.MisoString
  , syntaxes :: SyntaxTable
  , knownRules :: [P.NamedProp]
  , originalFocus :: Maybe focus
  , invalidates :: [MS.MisoString]  
  , renames :: [(MS.MisoString, MS.MisoString)]
  
  }

type Controller focus a = ExceptT MS.MisoString (State (ControllerState focus)) a

runController :: Controller focus a -> MS.MisoString -> SyntaxTable -> [P.NamedProp] -> Maybe focus
              -> Either MS.MisoString (a, FocusOutcome focus, [MS.MisoString], [(MS.MisoString, MS.MisoString)])
runController act ed tbl prps foc = case runState (runExceptT act) (CS Clear ed tbl prps foc [] []) of
  (Right a, CS f _ _ _ _ iv rn) -> Right (a, f, iv, rn)
  (Left e, _) -> Left e

errorMessage :: MS.MisoString -> Controller focus a
errorMessage str = throwError str

clearFocus :: Controller focus ()
clearFocus = modify (\(CS ff txt sy prps foc inv rn) -> CS Clear txt sy prps foc inv rn)

setFocusWithLeaving :: focus -> Controller focus ()
setFocusWithLeaving f = modify (\(CS ff txt sy prps foc inv rn) -> CS (Leave f) txt sy prps foc inv rn)


setFocus :: focus -> Controller focus ()
setFocus f = modify (\(CS ff txt sy prps foc inv rn) -> CS (Switch f) txt sy prps foc inv rn)

getOriginalFocus :: Controller focus (Maybe focus)
getOriginalFocus = originalFocus <$> get

getKnownRules :: Controller focus [P.NamedProp]
getKnownRules = knownRules <$> get

textInput :: Controller focus MS.MisoString
textInput = editing <$> get

syntaxTable :: Controller focus SyntaxTable
syntaxTable = syntaxes <$> get

invalidate :: MS.MisoString -> Controller focus ()
invalidate n = modify (\(CS ff txt sy prps foc inv  rn) -> (CS ff txt sy prps foc (n : inv) rn))

renameResource :: MS.MisoString -> MS.MisoString -> Controller focus ()
renameResource n m = modify (\(CS ff txt sy prps foc inv rn) -> (CS ff txt sy prps foc inv ((n, m) : rn)))

zoomFocus :: (focus -> focus') -> (focus' -> Maybe focus) -> Controller focus a -> Controller focus' a
zoomFocus f f' act = do
  CS sf ed sy prps foc inv rn <- get
  case runState (runExceptT act) (CS Clear ed sy prps (f' =<< foc) inv rn) of
    (Left e, _) -> errorMessage e
    (Right a, (CS sf' ed' sy' prps' foc' inv' rn')) -> put (CS (fmap f sf') ed' sy' prps' (fmap f foc') inv' rn') >> pure a

noFocus :: Controller focus a -> Controller () a
noFocus = zoomFocus (const ()) (const Nothing)

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
  defined :: s -> [P.NamedProp]
  defined = const []  
  inserted :: s -> Focus s
  definedSyntax :: s -> SyntaxTable
  definedSyntax = const []  
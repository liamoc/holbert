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
  , newnames :: [MS.MisoString]
  }

type Controller focus a = ExceptT MS.MisoString (State (ControllerState focus)) a

runController :: Controller focus a -> MS.MisoString -> SyntaxTable -> [P.NamedProp] -> Maybe focus
              -> Either MS.MisoString (a, FocusOutcome focus, [MS.MisoString], [(MS.MisoString, MS.MisoString)], [MS.MisoString])
runController act ed tbl prps foc = case runState (runExceptT act) (CS Clear ed tbl prps foc [] [] []) of
  (Right a, CS f _ _ _ _ iv rn nn) -> Right (a, f, iv, rn, nn)
  (Left e, _) -> Left e

errorMessage :: MS.MisoString -> Controller focus a
errorMessage str = throwError str

clearFocus :: Controller focus ()
clearFocus = modify (\(CS ff txt sy prps foc inv rn nn) -> CS Clear txt sy prps foc inv rn nn)

setFocusWithLeaving :: focus -> Controller focus ()
setFocusWithLeaving f = modify (\(CS ff txt sy prps foc inv rn nn) -> CS (Leave f) txt sy prps foc inv rn nn)


setFocus :: focus -> Controller focus ()
setFocus f = modify (\(CS ff txt sy prps foc inv rn nn) -> CS (Switch f) txt sy prps foc inv rn nn)

getOriginalFocus :: Controller focus (Maybe focus)
getOriginalFocus = originalFocus <$> get

getKnownRules :: Controller focus [P.NamedProp]
getKnownRules = knownRules <$> get

textInput :: Controller focus MS.MisoString
textInput = editing <$> get

syntaxTable :: Controller focus SyntaxTable
syntaxTable = syntaxes <$> get

anyInvalidated :: Controller focus Bool 
anyInvalidated = not . null . invalidates <$> get 

invalidate :: MS.MisoString -> Controller focus ()
invalidate n = modify (\(CS ff txt sy prps foc inv  rn nn) -> (CS ff txt sy prps foc (n : inv) rn nn))

renameResource :: MS.MisoString -> MS.MisoString -> Controller focus ()
renameResource n m = modify (\(CS ff txt sy prps foc inv rn nn) -> (CS ff txt sy prps foc inv ((n, m) : rn) nn))

newResource :: MS.MisoString  -> Controller focus ()
newResource n = modify (\(CS ff txt sy prps foc inv rn nn) -> (CS ff txt sy prps foc inv rn (n:nn)))


zoomFocus :: (focus -> focus') -> (focus' -> Maybe focus) -> Controller focus a -> Controller focus' a
zoomFocus f f' act = do
  CS sf ed sy prps foc inv rn nn <- get
  case runState (runExceptT act) (CS Clear ed sy prps (f' =<< foc) inv rn nn) of
    (Left e, _) -> errorMessage e
    (Right a, (CS sf' ed' sy' prps' foc' inv' rn' nn')) -> put (CS (fmap f sf') ed' sy' prps' (fmap f foc') inv' rn' nn') >> pure a

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
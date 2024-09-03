{-# LANGUAGE TypeFamilies, DeriveAnyClass, DeriveGeneric, OverloadedStrings #-}
module SyntaxDecl where
import Controller
import Miso.String as MS hiding (splitAt, length)
import GHC.Generics(Generic)
import Data.Aeson (ToJSON,FromJSON)
import StringRep 
import Data.Char

data SyntaxDecl = SyntaxDecl [(Int, MisoString, Associativity)]
  deriving (Show, Eq, Generic, ToJSON, FromJSON)


instance Control SyntaxDecl where
  data Focus SyntaxDecl = SelectName Int | SelectPrec Int
    deriving (Show, Eq)
  data Action SyntaxDecl = EditName Int | EditPrec Int | SetAssoc Associativity Int | RemoveDecl Int | AddDecl
    deriving (Show, Eq)

  editable _ (SelectName i) (SyntaxDecl ls) |  (_,s,_)   <- ls !! i = Just s
  editable _ (SelectPrec i) (SyntaxDecl ls) |  (p, _, _) <- ls !! i = Just (MS.pack $ show p)
  editable _ _ _ = Nothing

  leaveFocus _ = pure

  handle (SetAssoc a i) (SyntaxDecl ls) =  do
    let (lefts,(p,s,_):rights) = splitAt i ls
    pure (SyntaxDecl (lefts ++ (p, s, a):rights))
  handle (EditPrec i) (SyntaxDecl ls) = do
    let (lefts,(_,s,a):rights) = splitAt i ls
    new <- textInput
    let p = read $ MS.unpack new
    pure (SyntaxDecl (lefts ++ (p,s,a):rights))
  handle (EditName i) (SyntaxDecl ls) = do 
    let (lefts,(p,s,a):rights) = splitAt i ls
    new <- textInput
    case new of 
        "" -> errorMessage "Syntax cannot be empty"
        _ | MS.any Data.Char.isSpace new -> errorMessage "Syntax cannot contain spaces"
        _ | not (MS.any (=='_') new) -> errorMessage "Syntax must contain at least one underscore"
        _ -> pure ()
        --  Check for notation conflicts?
    pure (SyntaxDecl (lefts++ (p,new,a):rights))
  handle (RemoveDecl i) (SyntaxDecl ls) = do 
    let (lefts,_:rights) = splitAt i ls
    pure (SyntaxDecl (lefts++rights))
  handle (AddDecl) (SyntaxDecl ls) = do
    setFocus (SelectName (length ls)) 
    pure (SyntaxDecl (ls ++ [(0,"???",NonAssoc)]))

  inserted _ = SelectName 0

  definedSyntax (SyntaxDecl ls) = ls

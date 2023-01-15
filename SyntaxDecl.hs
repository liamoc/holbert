{-# LANGUAGE TypeFamilies, DeriveAnyClass, DeriveGeneric, OverloadedStrings #-}
module SyntaxDecl where
import Controller
import Miso.String as MS
import GHC.Generics(Generic)
import Data.Aeson (ToJSON,FromJSON)
import StringRep 
import Data.Char

data SyntaxDecl = SyntaxDecl Int MisoString Associativity
  deriving (Show, Eq, Generic, ToJSON, FromJSON)


instance Control SyntaxDecl where
  data Focus SyntaxDecl = SelectName | SelectPrec
    deriving (Show, Eq)
  data Action SyntaxDecl = EditName | EditPrec | SetAssoc Associativity
    deriving (Show, Eq)

  editable _ SelectName (SyntaxDecl _ s _) = Just s
  editable _ SelectPrec (SyntaxDecl i _  _) = Just (MS.pack $ show i)

  leaveFocus _ = pure

  handle (SetAssoc a) (SyntaxDecl i s _) = 
    pure (SyntaxDecl i s a)
  handle EditPrec (SyntaxDecl _ s a) = do
    new <- textInput
    let i = read $ MS.unpack new
    pure (SyntaxDecl i s a)
  handle EditName s@(SyntaxDecl i _ assoc) = do 
    new <- textInput
    case new of 
        "" -> errorMessage "Syntax cannot be empty"
        _ | MS.any Data.Char.isSpace new -> errorMessage "Syntax cannot contain spaces"
        _ | not (MS.any (=='_') new) -> errorMessage "Syntax must contain at least one underscore"
        _ -> pure ()
        --  Check for notation conflicts?
    pure (SyntaxDecl i new assoc)
  inserted _ = SelectName

  definedSyntax (SyntaxDecl i s a) = [(i,s,a)]

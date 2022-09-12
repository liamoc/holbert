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
  data Focus SyntaxDecl = Select
    deriving (Show, Eq)
  data Action SyntaxDecl = Edit
    deriving (Show, Eq)

  editable _ Select (SyntaxDecl _ s _) = Just s

  leaveFocus _ = pure

  handle Edit s@(SyntaxDecl i _ assoc) = do 
    new <- textInput
    case new of 
        "" -> errorMessage "Syntax cannot be empty"
        _ | MS.any Data.Char.isSpace new -> errorMessage "Syntax cannot contain spaces"
        _ | not (MS.any (=='_') new) -> errorMessage "Syntax must contain at least one underscore"
        _ -> pure ()
        --  Check for notation conflicts?
    pure (SyntaxDecl i new assoc)
  inserted _ = Select

  definedSyntax (SyntaxDecl i s a) = [(i,s,a)]
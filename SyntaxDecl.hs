{-# LANGUAGE TypeFamilies, DeriveGeneric, DeriveAnyClass, OverloadedStrings #-}
module SyntaxDecl where
import qualified Miso.String as MS
import Controller
import Data.Char
import Control.Applicative hiding (Const)
import StringRep
import GHC.Generics(Generic)
import qualified Data.Text as T
import Data.Aeson (ToJSON,FromJSON,toJSON,parseJSON,Value(..))
import qualified Text.Earley.Mixfix as EPM
data SyntaxDecl = SyntaxDecl MS.MisoString Int EPM.Associativity SyntaxTable deriving (Show, Eq, Generic, ToJSON, FromJSON)

instance ToJSON EPM.Associativity where
  toJSON (EPM.LeftAssoc) = String "Left"
  toJSON (EPM.RightAssoc) = String "Right"
  toJSON (EPM.NonAssoc) = String "Non"

instance FromJSON EPM.Associativity where
  parseJSON (String s) = case T.unpack s of
    "Left" -> return EPM.LeftAssoc
    "Right" -> return EPM.RightAssoc
    "Non" -> return EPM.NonAssoc
    _ -> error $ "Json format not expected"
  parseJSON _ =  error $ "Json format not expected"

legalAssocStr :: [(MS.MisoString, EPM.Associativity)]
legalAssocStr = [("Left", EPM.LeftAssoc), ("Right", EPM.RightAssoc), ("Non", EPM.NonAssoc)]

matchAssoc :: MS.MisoString -> Maybe EPM.Associativity
matchAssoc s = case lookup s legalAssocStr of
  Just a -> Just a
  Nothing -> Nothing

matchStr :: EPM.Associativity -> Maybe MS.MisoString
matchStr a = case lookup a (map (\(s,a) -> (a,s)) legalAssocStr) of
  Just s -> Just s
  Nothing -> Nothing

checkAssoc :: MS.MisoString -> Controller (Focus SyntaxDecl) EPM.Associativity
checkAssoc new = case matchAssoc new of
  Just a  -> pure a
  Nothing -> errorMessage $ "Invalid associativity name: " <> new

checkPrec :: MS.MisoString -> Controller (Focus SyntaxDecl) ()
checkPrec prec = case and $ go prec of
  True -> pure ()
  False -> errorMessage "Precedence must be integer"
  where
    go :: MS.MisoString -> [Bool]
    go prec = case MS.uncons prec of
      Just (x, "") -> [isDigit x]
      Just (x, xs) -> (isDigit x) : go xs

instance Control SyntaxDecl where
  data Focus SyntaxDecl = NewSyntaxDeclFocus
                        | NameFocus
                        | PrecFocus
                        | AssocFocus
                        deriving (Show, Eq)
  data Action SyntaxDecl = AddSyntaxDecl
                         | EditName
                         | EditPrec
                         | EditAssoc
                         deriving (Show, Eq)

  editable tbl NameFocus (SyntaxDecl n p a t) = Just n
  editable tbl PrecFocus (SyntaxDecl n p a t) = Just $ MS.toMisoString $ show p
  editable tbl AssocFocus (SyntaxDecl n p a t) = Just $ MS.toMisoString $ show a

  leaveFocus NewSyntaxDeclFocus = noFocus . handle AddSyntaxDecl
  leaveFocus NameFocus = noFocus . handle EditName
  leaveFocus PrecFocus = noFocus . handle EditPrec
  leaveFocus AssocFocus = noFocus . handle EditAssoc

  handle AddSyntaxDecl _ = do
    new <- textInput
    tbl <- syntaxTable
    setFocus NameFocus
    pure $ SyntaxDecl new 0 EPM.NonAssoc tbl

  handle EditName (SyntaxDecl _ p a t) = do
    new <- textInput
    pure $ SyntaxDecl new p a t

  handle EditPrec (SyntaxDecl n _ a t) = do
    new <- textInput
    checkPrec new
    pure $ SyntaxDecl n ((MS.fromMisoString new) :: Int) a t

  handle EditAssoc (SyntaxDecl n p _ t) = do
    new <- textInput
    a <- checkAssoc new
    pure $ SyntaxDecl n p a t

  inserted _ = NewSyntaxDeclFocus

  definedSyntax (SyntaxDecl n p a tbl) = (p, n, a):tbl
{-# LANGUAGE TypeFamilies, DeriveGeneric, DeriveAnyClass #-}
module Item where

import qualified Rule as R
import qualified Heading as H
import qualified Paragraph as P
import qualified SyntaxDecl as S
import Controller
import GHC.Generics(Generic)
import Data.Aeson (ToJSON,FromJSON)
import Optics.Core

data Item = Rule R.Rule
          | Heading H.Heading
          | Paragraph P.Paragraph
          | SyntaxDecl S.SyntaxDecl
          deriving (Show, Eq, Generic, ToJSON, FromJSON)


rule :: Prism' Item R.Rule
rule = prism Rule $ \ x ->
         case x of 
           Rule r -> Right r
           _      -> Left  x


heading :: Prism' Item H.Heading
heading = prism Heading $ \ x ->
          case x of 
            Heading r -> Right r
            _         -> Left  x


paragraph :: Prism' Item P.Paragraph
paragraph = prism Paragraph $ \ x ->
            case x of 
              Paragraph r -> Right r
              _           -> Left  x

syntaxdecl :: Prism' Item S.SyntaxDecl
syntaxdecl = prism SyntaxDecl $ \ x ->
            case x of 
              SyntaxDecl r -> Right r
              _            -> Left  x

instance Control Item where
  data Action Item = RuleAct (Action R.Rule)
                   | HeadingAct (Action H.Heading)
                   | ParagraphAct (Action P.Paragraph)
                   | SyntaxDeclAct (Action S.SyntaxDecl)
                   deriving (Show, Eq)

  data Focus Item = RuleFocus (Focus R.Rule)
                  | HeadingFocus (Focus H.Heading)
                  | ParagraphFocus (Focus P.Paragraph)
                  | SyntaxDeclFocus (Focus S.SyntaxDecl)
                  deriving (Show, Eq)
 

  renamed n (Heading i)    = Heading    $ renamed n i
  renamed n (Rule i)       = Rule       $ renamed n i
  renamed n (Paragraph i)  = Paragraph  $ renamed n i
  renamed n (SyntaxDecl i) = SyntaxDecl $ renamed n i

  defined (Heading i)    = defined i
  defined (Rule i)       = defined i
  defined (Paragraph i)  = defined i
  defined (SyntaxDecl i) = defined i

  definedSyntax (Heading i)    = definedSyntax i
  definedSyntax (Rule i)       = definedSyntax i
  definedSyntax (Paragraph i)  = definedSyntax i
  definedSyntax (SyntaxDecl i) = definedSyntax i

  invalidated n (Heading i)    = Heading   $ invalidated n i
  invalidated n (Rule i)       = Rule      $ invalidated n i
  invalidated n (Paragraph i)  = Paragraph $ invalidated n i
  invalidated n (SyntaxDecl i) = SyntaxDecl $ invalidated n i
  
  editable tbl (HeadingFocus f)    (Heading h)    = editable tbl f h
  editable tbl (RuleFocus f)       (Rule h)       = editable tbl f h
  editable tbl (ParagraphFocus f)  (Paragraph h)  = editable tbl f h
  editable tbl (SyntaxDeclFocus f) (SyntaxDecl h) = editable tbl f h

  leaveFocus (HeadingFocus f)      (Heading h)    = Heading    <$> leaveFocus f h
  leaveFocus (ParagraphFocus f)    (Paragraph h)  = Paragraph  <$> leaveFocus f h
  leaveFocus (RuleFocus f)         (Rule h)       = Rule       <$> leaveFocus f h
  leaveFocus (SyntaxDeclFocus f)   (SyntaxDecl h) = SyntaxDecl <$> leaveFocus f h

  handle (HeadingAct a)    (Heading s)    = fmap Heading    . zoomFocus HeadingFocus    (\x -> case x of (HeadingFocus f) -> Just f; _ -> Nothing) $ handle a s
  handle (ParagraphAct a)  (Paragraph s)  = fmap Paragraph  . zoomFocus ParagraphFocus  (\x -> case x of (ParagraphFocus f) -> Just f; _ -> Nothing) $ handle a s
  handle (RuleAct a)       (Rule s)       = fmap Rule       . zoomFocus RuleFocus       (\x -> case x of (RuleFocus f) -> Just f; _ -> Nothing) $ handle a s
  handle (SyntaxDeclAct a) (SyntaxDecl s) = fmap SyntaxDecl . zoomFocus SyntaxDeclFocus (\x -> case x of (SyntaxDeclFocus f) -> Just f; _ -> Nothing) $ handle a s

  inserted (Heading s)    = HeadingFocus    (inserted s)
  inserted (Paragraph s)  = ParagraphFocus  (inserted s)
  inserted (Rule s)       = RuleFocus       (inserted s)
  inserted (SyntaxDecl s) = SyntaxDeclFocus (inserted s)

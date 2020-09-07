{-# LANGUAGE TypeFamilies #-}
module Item where

import qualified Rule as R
import qualified Heading as H
import qualified Paragraph as P
import Controller

import Optics.Core

data Item = Rule R.Rule
          | Heading H.Heading
          | Paragraph P.Paragraph
          deriving (Show, Eq)


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

instance Control Item where
  data Action Item = RuleAct (Action R.Rule)
                   | HeadingAct (Action H.Heading)
                   | ParagraphAct (Action P.Paragraph)
                   deriving (Show, Eq)

  data Focus Item = RuleFocus (Focus R.Rule)
                  | HeadingFocus (Focus H.Heading)
                  | ParagraphFocus (Focus P.Paragraph)
                  deriving (Show, Eq)
 

  renamed n (Heading i)   = Heading   $ renamed n i
  renamed n (Rule i)      = Rule      $ renamed n i
  renamed n (Paragraph i) = Paragraph $ renamed n i

  defined (Heading i)   = defined i
  defined (Rule i)      = defined i
  defined (Paragraph i) = defined i

  invalidated n (Heading i)   = Heading   $ invalidated n i
  invalidated n (Rule i)      = Rule      $ invalidated n i
  invalidated n (Paragraph i) = Paragraph $ invalidated n i
  
  editable (HeadingFocus f)   (Heading h)   = editable f h
  editable (RuleFocus f)      (Rule h)      = editable f h
  editable (ParagraphFocus f) (Paragraph h) = editable f h

  leaveFocus (HeadingFocus f)   (Heading h)   = Heading   <$> leaveFocus f h
  leaveFocus (ParagraphFocus f) (Paragraph h) = Paragraph <$> leaveFocus f h
  leaveFocus (RuleFocus f)      (Rule h)      = Rule      <$> leaveFocus f h

  handle (HeadingAct a)   (Heading s)   = fmap Heading   . zoomFocus HeadingFocus   $ handle a s
  handle (ParagraphAct a) (Paragraph s) = fmap Paragraph . zoomFocus ParagraphFocus $ handle a s
  handle (RuleAct a)      (Rule s)      = fmap Rule      . zoomFocus RuleFocus      $ handle a s

  inserted (Heading s)   = HeadingFocus   (inserted s)
  inserted (Paragraph s) = ParagraphFocus (inserted s)
  inserted (Rule s)      = RuleFocus      (inserted s)


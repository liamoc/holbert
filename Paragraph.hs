{-# LANGUAGE TypeFamilies #-}
module Paragraph where
import Miso.String
import Controller
data Paragraph = Paragraph MisoString deriving (Show, Eq)

instance Control Paragraph where
  data Focus Paragraph = Select
    deriving (Show, Eq)
  data Action Paragraph = Edit
    deriving (Show, Eq)

  editable Select (Paragraph s) = Just s

  leaveFocus _ = pure

  handle Edit _ = Paragraph . pack <$> textInput

  inserted _ = Select

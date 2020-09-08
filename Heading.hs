{-# LANGUAGE TypeFamilies #-}
module Heading where
import Controller
import Miso.String

data Heading = Heading Int MisoString deriving (Show, Eq)

instance Control Heading where
  data Focus Heading = Select
    deriving (Show, Eq)
  data Action Heading = Edit
    deriving (Show, Eq)

  editable Select (Heading i s) = Just s

  leaveFocus _ = pure

  handle Edit (Heading i _) = Heading i . pack <$> textInput

  inserted _ = Select
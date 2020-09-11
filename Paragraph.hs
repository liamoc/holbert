{-# LANGUAGE TypeFamilies, DeriveGeneric, DeriveAnyClass #-}
module Paragraph where
import Miso.String
import Controller
import GHC.Generics(Generic)
import Data.Aeson (ToJSON,FromJSON)
data Paragraph = Paragraph MisoString deriving (Show, Eq, Generic, ToJSON, FromJSON)

instance Control Paragraph where
  data Focus Paragraph = Select
    deriving (Show, Eq)
  data Action Paragraph = Edit
    deriving (Show, Eq)

  editable Select (Paragraph s) = Just s

  leaveFocus _ = pure

  handle Edit _ = Paragraph <$> textInput

  inserted _ = Select

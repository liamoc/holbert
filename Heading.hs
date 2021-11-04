{-# LANGUAGE TypeFamilies, DeriveAnyClass, DeriveGeneric #-}
module Heading where
import Controller
import Miso.String
import GHC.Generics(Generic)
import Data.Aeson (ToJSON,FromJSON)

data Heading = Heading Int MisoString 
  deriving (Show, Eq, Generic, ToJSON, FromJSON)

instance Control Heading where
  data Focus Heading = Select
    deriving (Show, Eq)
  data Action Heading = Edit
    deriving (Show, Eq)

  editable _ Select (Heading i s) = Just s

  leaveFocus _ = pure

  handle Edit (Heading i _) = Heading i <$> textInput

  inserted _ = Select
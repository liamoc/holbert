{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
module Main where
import Miso
import Editor (runAction, EditorAction (..), Editor (..), initialEditor)
import qualified ImportExport
import View.Editor (viewEditor)
main :: IO ()
main = startApp App {..}
  where
    initialAction = Import
    model         = initialEditor
    update        = updateModel
    view          = viewEditor
    events        = defaultEvents
    subs          = []
    mountPoint    = Nothing
    logLevel      = Off

updateModel :: EditorAction -> Editor -> Effect EditorAction Editor
updateModel Import = \m -> act m #> m 
  where
    act m = do
      x <- ImportExport.import_ (inputText m)
      pure $ case x of 
        Left e -> DisplayError e 
        Right x -> LoadDocument x
updateModel Download = \m -> act m #> m
  where act m = ImportExport.export "file.holbert" (document m) >> pure Noop
updateModel act = noEff . runAction act


{-# LANGUAGE RecordWildCards, OverloadedStrings #-}
module Main where
import Miso
import Miso.String(MisoString)
import Editor (runAction, EditorAction (..), Editor (..), initialEditor)
import qualified ImportExport
import View.Editor (viewEditor)


foreign import javascript unsafe "$r = document.location.search.slice(1);"
  urlparameter :: IO MisoString

main :: IO ()
main = do 
  url <- (\x -> if x == "" then "index.holbert" else x) <$> urlparameter
  startApp App {model = initialEditor url, ..}
  where
    initialAction = Import
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


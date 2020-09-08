{-# LANGUAGE RecordWildCards #-}
module Main where
import Miso
import Controller
import Editor
import View.Editor


main :: IO ()
main = startApp App {..}
  where
    initialAction = Reset
    model         = initialEditor
    update        = updateModel
    view          = viewEditor
    events        = defaultEvents
    subs          = []
    mountPoint    = Nothing
    logLevel      = Off

updateModel :: EditorAction -> Editor -> Effect EditorAction Editor
updateModel act ed = noEff $ runAction act ed


{-# LANGUAGE RecordWildCards #-}
module Main where
import Miso
import Editor (runAction, EditorAction (Reset), Editor, initialEditor)
import View.Editor (viewEditor)

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
updateModel act = noEff . runAction act


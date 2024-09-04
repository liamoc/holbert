{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE JavaScriptFFI #-}
module ImportExport where
-- Vandelay Industries
import Miso
import Data.JSString
import JavaScript.Web.XMLHttpRequest
import Data.Aeson
import GHCJS.Marshal
import qualified Control.Exception as Exc


cleanup :: IO a -> IO (Maybe a)
cleanup x = Exc.catch (Just <$> x) handler
  where
    handler exc = return Nothing  `const`  (exc :: Exc.ErrorCall)

import_ :: (FromJSON a) => JSString -> IO (Either JSString a)
import_ url = do
  response <- xhr $ Request GET url Nothing [] False NoData
  case status response of
    200 ->
      case contents response of
        Nothing -> pure $ Left "empty response"
        Just s  -> do
          s' <- cleanup . parse =<< toJSVal (s :: JSString)
          pure $ case s' of
            Nothing -> Left "cannot parse file"
            Just r  -> Right r
    _ -> pure $ Left "Unsuccessful status code"

export :: (ToJSON a) => JSString -> a -> IO ()
export fn m = stringify m >>= saveAs fn

openFile :: (FromJSON a) => IO (Either JSString a)
openFile = do
  str <- fileOpenHelper
  s' <- cleanup . parse =<< toJSVal (str :: JSString)
  pure $ case s' of
    Nothing -> Left "cannot parse file"
    Just r  -> Right r

foreign import javascript interruptible
  "fileSave(new Blob([$2],{type:'application/json'}),{fileName:$1,extensions:['.holbert']}).then($c);"
  saveAs :: JSString -> JSString -> IO ()
foreign import javascript interruptible
    "fileOpenHelper().then($c);"
    fileOpenHelper :: IO JSString

{-# LANGUAGE OverloadedStrings #-}
module StringRep (toSexps, fromSexps) where

import Data.Char
import Control.Monad(ap, when)
import Data.List
import Prelude hiding (lex)
import Data.Maybe
import Control.Monad.Except
import Control.Applicative hiding (Const)
import Control.Monad.State
import qualified Miso.String as MS
import qualified Data.Text.Lazy.Builder as B
import qualified Data.Text.Lazy as L
import Terms

type Error = MS.MisoString

toSexps :: [Name] -> Term -> MS.MisoString 
toSexps ctx t = MS.ms $ B.toLazyText $ go ctx t
go :: [Name] -> Term -> B.Builder 
go ctx (Lam (M x) t) = B.fromText (MS.fromMisoString x) <> ". " <> go (x:ctx) t
go ctx e = go' ctx e
go' ctx (Ap a1 a2) = go' ctx a1 <> " " <> go'' ctx a2
go' ctx (Lam n t) = "(" <> go ctx (Lam n t) <> ")"
go' ctx e = go'' ctx e
go'' ctx (LocalVar v) = B.fromText (MS.fromMisoString (ctx !! v))
go'' ctx (Const id) = B.fromText $ MS.fromMisoString $ id
go'' ctx (MetaVar id) = "?" <> B.fromText (MS.fromMisoString $ MS.pack (show id))
go'' ctx e = "(" <> go ctx e <> ")"

data Token = LParen | RParen | Word MS.MisoString | Dot | Binder MS.MisoString deriving (Show, Eq)

lexer :: MS.MisoString -> [Token]
lexer str | (x,y) <- MS.span isSpace str
          , not (MS.null x) = lexer y
lexer str = case MS.uncons str of 
  Nothing -> []
  Just ('(',rest) -> LParen:lexer rest 
  Just (')',rest) -> RParen:lexer rest 
  Just ('.',rest) -> Dot:lexer rest 
  _ | (word,rest) <- MS.span (\c -> not (isSpace c) && c `notElem` ("()." :: String)) str 
   -> Word word : lexer rest

preprocess (Word s : Dot : rest) = Binder s : preprocess rest
preprocess (x:xs) = x : preprocess xs
preprocess [] = []

unlex LParen = "("
unlex RParen = ")"
unlex Dot = "."
unlex (Binder s) = s <> "."
unlex (Word s) = s


type Parser a = ExceptT MS.MisoString (State [Token]) a

runParser = runState . runExceptT

expect :: Token -> Parser ()
expect t = do
  w <- lex
  if w == t then pure () else parseError $ "Expected '" <> unlex t <> "', got '" <> unlex w <> "'."

lex :: Parser Token
lex = do
  xs' <- get
  when (null xs') (parseError $ "Unexpected end of input")
  let (x:xs) = xs'
  put xs
  pure x

peek :: Parser (Maybe Token)
peek = do
  xs <- get
  pure $ listToMaybe xs

parseError :: MS.MisoString -> Parser a
parseError str = throwError str
parser :: [Name] -> Parser Term
parser ctx = do
      w <- peek
      case w of
        Just (Binder w) -> lex >> (Lam (M w) <$> parser (w:ctx))
        _ -> parser' ctx

parser' :: [Name] -> Parser Term
parser' ctx = toApplications <$> some (parser'' ctx)
  where
    toApplications [] = error "impossible"
    toApplications [x] = x
    toApplications [x,y] = Ap x y
    toApplications (x:y:ys) = toApplications (Ap x y:ys)


parser'' :: [Name] -> Parser Term
parser'' ctx = do
      w <- peek
      case w of Just (Word w) -> lex >> pure (symbol w)
                Just (LParen) -> do lex; x <- parser ctx; expect RParen;  pure x
                Just x        -> parseError ("Unexpected '" <> unlex x <> "'")
                Nothing       -> parseError ("Unexpected end of input")
  where symbol w | Just v <- elemIndex w ctx = LocalVar v
                 | otherwise = Const w

fromSexps :: [Name] -> MS.MisoString -> Either Error Term
fromSexps ctx s = case runParser (parser ctx) . preprocess . lexer $ s of
              (Left e,_) -> Left e
              (Right v,[]) -> Right v
              (_,s) -> Left $ "Parse error: Leftover '" <> MS.concat (map unlex s) <> "'"

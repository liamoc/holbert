module StringRep (toSexps, fromSexps) where

import Data.Char
import Control.Monad(ap, when)
import Data.List
import Prelude hiding (lex)
import Data.Maybe
import Control.Monad.Except
import Control.Applicative hiding (Const)
import Control.Monad.State

import Terms

toSexps :: [String] -> Term -> String
toSexps ctx (Lam (M x) t) = x ++ ". " ++ toSexps (x:ctx) t 
toSexps ctx e = toSexps' ctx e
toSexps' ctx (Ap a1 a2)    = toSexps' ctx a1 ++ " " ++ toSexps'' ctx a2
toSexps' ctx (Lam n t)    = "(" ++ toSexps ctx (Lam n t) ++ ")"
toSexps' ctx e = toSexps'' ctx e
toSexps'' ctx (LocalVar v) = ctx !! v
toSexps'' ctx (Const id) = id
toSexps'' ctx (MetaVar id) = "?" ++ show id
toSexps'' ctx e = "(" ++ toSexps ctx e ++ ")"
 
data Token = LParen | RParen | Word String | Dot | Binder String deriving (Show, Eq)

lexer :: String -> [Token]
lexer [] =  []
lexer ('(':rest) = LParen:lexer rest
lexer (')':rest) = RParen:lexer rest
lexer ('.':rest) = Dot:lexer rest
lexer (c:rest) | isSpace c = lexer rest
lexer str | (word,rest) <- span (\c -> not (isSpace c) && c `notElem` "().") str 
          = Word word : lexer rest

preprocess (Word s : Dot : rest) = Binder s : preprocess rest
preprocess (x:xs) = x : preprocess xs
preprocess [] = []

unlex LParen = "("
unlex RParen = ")"
unlex Dot = "."
unlex (Binder s) = s ++ "."
unlex (Word s) = s


type Parser a = ExceptT String (State [Token]) a

runParser = runState . runExceptT

expect :: Token -> Parser ()
expect t = do
  w <- lex
  if w == t then pure () else parseError $ "Expected '" ++ unlex t ++ "', got '" ++ unlex w ++ "'."

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

parseError :: String -> Parser a
parseError str = throwError str
parser :: [String] -> Parser Term
parser ctx = do
      w <- peek
      case w of 
        Just (Binder w) -> lex >> (Lam (M w) <$> parser (w:ctx))
        _ -> parser' ctx

parser' :: [String] -> Parser Term
parser' ctx = toApplications <$> some (parser'' ctx)
  where
    toApplications [] = error "impossible"
    toApplications [x] = x
    toApplications [x,y] = Ap x y
    toApplications (x:y:ys) = toApplications (Ap x y:ys)

parser'' :: [String] -> Parser Term
parser'' ctx = do 
      w <- peek
      case w of Just (Word w) -> lex >> pure (symbol w)
                Just (LParen) -> do lex; x <- parser ctx; expect RParen;  pure x
                Just x        -> parseError ("Unexpected '" ++ unlex x ++ "'")
                Nothing       -> parseError ("Unexpected end of input")
  where symbol w | Just v <- elemIndex w ctx = LocalVar v
                 | otherwise = Const w
           
fromSexps :: [String] -> String -> Either String Term
fromSexps ctx s = case runParser (parser ctx) . preprocess . lexer $ s of 
              (Left e,_) -> Left e
              (Right v,[]) -> Right v
              (_,s) -> Left $ "Parse error: Leftover '" ++ concatMap unlex s ++ "'"

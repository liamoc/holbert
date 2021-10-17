{-# LANGUAGE OverloadedStrings, RecursiveDo, CPP #-}
module StringRep (prettyPrint, parse) where

import Data.Char
import Control.Arrow(first)
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
import qualified Text.Earley as EP
import qualified Text.Earley.Mixfix as EPM

data Token = LParen | RParen | Word MS.MisoString | Dot | Binder MS.MisoString deriving (Show, Eq)

holey :: String -> EPM.Holey MS.MisoString
holey ""       = []
holey ('_':xs) = Nothing : holey xs
holey xs       = Just (MS.toMisoString i) : holey rest
  where (i, rest) = span (/= '_') xs

concatMixfix :: EPM.Holey Token -> MS.MisoString
concatMixfix xs = MS.ms $ B.toLazyText $ go xs
  where
    go []            = B.fromText ""
    go (Nothing:xs)  = B.fromText "_" <> go xs
    go ((Just (Word x)):xs) = (B.fromText $ MS.fromMisoString x) <> go xs

mixfixDef :: [[(String, EPM.Associativity)]]
mixfixDef = [ [("_->_",          EPM.RightAssoc)]
            , [("_,_",           EPM.NonAssoc)]
            , [("if_then_else_", EPM.RightAssoc)]
            , [("_|-_:_",        EPM.NonAssoc)]
            , [("_+_",           EPM.LeftAssoc)]
            , [("_*_",           EPM.LeftAssoc)]
            ]

mixfixTable :: [[(EPM.Holey MS.MisoString, EPM.Associativity)]]
mixfixTable = (map . map) (first holey) mixfixDef

grammar :: EP.Grammar r (EP.Prod r Token Token Term)
grammar = mdo
  ident     <- EP.rule $ getWord <$> EP.satisfy isLegalWord
  atom      <- EP.rule $ Const <$> ident
                      <|> EP.namedToken LParen *> program <* EP.namedToken RParen
  normalApp <- EP.rule $ atom
                      <|> Ap <$> normalApp <*> atom
  mixfixApp <- EPM.mixfixExpression table normalApp mixfixCon
  program   <- EP.rule $ mixfixApp 
                      <|> Lam . maskCon <$> EP.satisfy isLegalBinder <*> program 
  return program
  where
    maskCon (Binder b) = M b
    mixfixCon op ts = applyApTelescope (Const $ concatMixfix op) ts
    getWord (Word w) = w
    table = map (map $ first $ map $ fmap (EP.namedToken . Word)) mixfixTable
    illegalIdents = [s | xs <- mixfixTable , (ys, _) <- xs , Just s <- ys]
    isLegalBinder (Binder b) = not $ elem b illegalIdents
    isLegalBinder _ = False
    isLegalWord (Word w) = not $ elem w illegalIdents 
    isLegalWord _ = False

postProc :: [Name] -> Term -> Term
postProc ctx (Lam (M b) t) = Lam (M b) $ postProc (b:ctx) t
postProc ctx (Ap t1 t2) = Ap (postProc ctx t1) (postProc ctx t2) 
postProc ctx (Const x) | Just v <- elemIndex x ctx = LocalVar v
                       | otherwise = Const x

type Error = MS.MisoString

printHoley :: MS.MisoString -> [B.Builder] -> B.Builder
printHoley origin operends = go origin origin operends
  where
    go origin op [] = B.fromText $ MS.fromMisoString op
    go origin op (x:xs) = case MS.uncons op of 
      Just ('_', ops) | origin == op -> x <> " " <> go origin ops xs
                      | ops == "" -> " " <> x <> go origin ops xs
                      | otherwise -> " " <> x <> " " <> go origin ops xs
      Just (o, ops) -> B.singleton o <> go origin ops (x:xs)

prettyPrint :: [Name] -> Term -> MS.MisoString 
prettyPrint ctx t = MS.ms $ B.toLazyText $ go ctx t
go :: [Name] -> Term -> B.Builder 
go ctx (Lam (M x) t) = B.fromText (MS.fromMisoString x) <> ". " <> go (x:ctx) t
go ctx e = go' ctx e
go' ctx (Ap a1 a2) 
  | (x, ts) <- peelApTelescope (Ap a1 a2) = case x of 
    Const op 
      | isMixfix op, MS.count "_" op == length ts -> printHoley op $ (map $ go'' ctx) ts
      | otherwise -> go' ctx a1 <> " " <> go'' ctx a2
        where
          isMixfix op = elem op [MS.toMisoString ys | xs <- mixfixDef, (ys, _) <- xs]  
go' ctx (Lam n t) = "(" <> go ctx (Lam n t) <> ")"
go' ctx e = go'' ctx e
go'' ctx (LocalVar v) = B.fromText (MS.fromMisoString (ctx !! v))
go'' ctx (Const id) = B.fromText $ MS.fromMisoString $ id
go'' ctx (MetaVar id) = "?" <> B.fromText (MS.fromMisoString $ MS.pack (show id))
go'' ctx e = "(" <> go ctx e <> ")"

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

fromMixfix :: [Name] -> MS.MisoString -> Either Error Term
fromMixfix ctx s = case EP.fullParses (EP.parser grammar) $ preprocess . lexer $ s of
                   ([], rep) -> Left $ "Parse error: unexpected character at position " <> MS.toMisoString (EP.position rep)
                   ([x], rep) -> Right $ postProc ctx x
                   ((x:xs), rep) -> Left $ "Parse error: ambiguous parsing result: " <> MS.concat (map ((prettyPrint ctx). (postProc ctx)) (x:xs))

parse :: [Name] -> MS.MisoString -> Either Error Term
#ifdef MIXFIX
parse = fromMixfix
#else
parse = fromSexps
#endif
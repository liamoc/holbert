{-# LANGUAGE OverloadedStrings, RecursiveDo, StandaloneDeriving, DeriveAnyClass, DeriveGeneric #-}
module StringRep (prettyPrint, parse, SyntaxTable (..), EPM.Associativity(..)) where

import Data.Char
import Control.Arrow(first)
import Control.Monad(ap, when)
import Data.List
import Data.Function (on)
import Data.Ord(comparing)
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
import Data.Aeson(ToJSON, FromJSON)
import GHC.Generics(Generic)
data Token = LParen | RParen | Word MS.MisoString | Dot | Binder MS.MisoString deriving (Show, Eq)
deriving instance Generic EPM.Associativity 
deriving instance FromJSON EPM.Associativity 
deriving instance ToJSON EPM.Associativity 
holey :: MS.MisoString -> EPM.Holey MS.MisoString
holey str = case MS.uncons str of 
  Nothing -> []
  Just ('_',xs) -> Nothing : holey xs
  Just _        -> Just (MS.toMisoString i) : holey rest
  where (i, rest) = MS.span (/= '_') str

concatMixfix :: EPM.Holey Token -> MS.MisoString
concatMixfix xs = MS.ms $ B.toLazyText $ go xs
  where
    go []            = B.fromText ""
    go (Nothing:xs)  = B.fromText "_" <> go xs
    go ((Just (Word x)):xs) = (B.fromText $ MS.fromMisoString x) <> go xs

type SyntaxTable = [(Int, MS.MisoString,EPM.Associativity)]


generateTable :: SyntaxTable -> [[(EPM.Holey MS.MisoString, EPM.Associativity)]]
generateTable tbl = (map . map) (\(_,str, a) -> (holey str, a)) $ groupBy ((==) `on` precedence) $ sortBy (comparing precedence) tbl
  where precedence (a,b,c) = a

grammar :: SyntaxTable -> EP.Grammar r (EP.Prod r Token Token Term)
grammar tbl = mdo
  ident     <- EP.rule $ getWord <$> EP.satisfy isLegalWord
  atom      <- EP.rule $ smartConst <$> ident
                      <|> EP.namedToken LParen *> program <* EP.namedToken RParen
  normalApp <- EP.rule $ atom
                      <|> Ap <$> normalApp <*> atom
  mixfixApp <- EPM.mixfixExpression table normalApp mixfixCon
  program   <- EP.rule $ mixfixApp 
                      <|> Lam . maskCon <$> EP.satisfy isLegalBinder <*> program 
  return program
  where
    maskCon (Binder b) = M b
    smartConst c = case MS.uncons c of
       Just ('@',xs) -> Const xs True
       _ -> Const c False
    mixfixCon op ts = applyApTelescope (smartConst $ concatMixfix op) ts
    getWord (Word w) = w
    tbl' = generateTable tbl
    table = map (map $ first $ map $ fmap (EP.namedToken . Word)) $ tbl'
    illegalIdents = [s | xs <- tbl' , (ys, _) <- xs , Just s <- ys]
    isLegalBinder (Binder b) = not $ elem b illegalIdents
    isLegalBinder _ = False
    isLegalWord (Word w) = not $ elem w illegalIdents 
    isLegalWord _ = False

postProc :: [Name] -> Term -> Term
postProc ctx (Lam (M b) t) = Lam (M b) $ postProc (b:ctx) t
postProc ctx (Ap t1 t2) = Ap (postProc ctx t1) (postProc ctx t2) 
postProc ctx (Const x False) | Just v <- elemIndex x ctx = LocalVar v
                             | otherwise = Const x False
postProc ctx (Const x True) = Const x True

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

prettyPrint :: SyntaxTable -> [Name] -> Term -> MS.MisoString 
prettyPrint tbl ctx t = MS.ms $ B.toLazyText $ go ctx t
  where
    go :: [Name] -> Term -> B.Builder 
    go ctx (Lam (M x) t) = B.fromText (MS.fromMisoString x) <> ". " <> go (x:ctx) t
    go ctx e = go' ctx e
    go' ctx (Ap a1 a2) 
      | (x, ts) <- peelApTelescope (Ap a1 a2) = case x of 
        Const op b 
          | isMixfix op b, MS.count "_" op == length ts -> printHoley (if b then "@" <> op else op) $ (map $ go'' ctx) ts
        _ -> go' ctx a1 <> " " <> go'' ctx a2
      where
        isMixfix op b = elem (if b then "@"<>op else op) [ys |  (_,ys, _) <- tbl]  
        
    go' ctx (Lam n t) = "(" <> go ctx (Lam n t) <> ")"
    go' ctx e = go'' ctx e
    go'' ctx (LocalVar v) = B.fromText (MS.fromMisoString (ctx !! v))
    go'' ctx (Const id c) = (if c then "@" else mempty) <> (B.fromText $ MS.fromMisoString $ id)
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

fromMixfix :: SyntaxTable -> [Name] -> MS.MisoString -> Either Error Term
fromMixfix tbl ctx s = case EP.fullParses (EP.parser $ grammar tbl) $ preprocess . lexer $ s of
  ([], rep) -> Left $ "Parse error: unexpected character at position " <> MS.toMisoString (EP.position rep)
  ([x], rep) -> Right $ postProc ctx x
  ((x:xs), rep) -> Left $ "Parse error: ambiguous parsing result: " <> MS.concat (map ((prettyPrint tbl ctx). (postProc ctx)) (x:xs))

parse :: SyntaxTable -> [Name] -> MS.MisoString -> Either Error Term
parse = fromMixfix

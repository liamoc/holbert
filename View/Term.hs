{-# LANGUAGE OverloadedStrings #-}
module View.Term where

import Terms
import Editor 
import View.Utils
import Miso hiding (on)
import Data.List (intersperse, dropWhileEnd, groupBy)

renderTerm = renderTermCtx [] 
renderTermCtx context opts trm = renderTerm' True context trm
  where
    renderTerm' outer ctx (Lam (M v) t) = binder v (renderTerm' True (v:ctx) t)
    renderTerm' outer ctx other = renderTerm'' outer ctx other 

    renderTerm'' outer ctx t 
      | Lam _ _ <- t = multi $ parenthesise [renderTerm' False ctx t]
      | (x, ts, []) <- peelApTelescope' t = case x of 
           LocalVar j 
              | j >= length ctx -> boundName (show j)
              | length ctx - j <= length context -> freevar (ctx !! j) -- , sub_ [] [text (pack $ show j)]]
              | otherwise -> boundName (ctx !! j)
           MetaVar i -> metavar i (renderITelescope ts)
           Const s -> constant s
              | (Const n, [], args) <- peelApTelescope' t
              , showInfixes opts
              , length (filter (== '_') n) == length args = multi $ (if outer then id else parenthesise) $ intersperse space (infixTerms n args)
      | (x, ts, args) <- peelApTelescope' t = 
              multi $ (if outer then id else parenthesise) 
                    $ renderTerm'' False ctx x : renderITelescope ts ++ space : intersperse space (map (renderTerm'' False ctx) args)
      where 
        parenthesise = ([inline "parens" [text "("]] ++) . (++ [inline "parens" [text ")"]])
        infixTerms [] [] = []
        infixTerms str [] = [constant str]
        infixTerms ('_':str) (x:xs) = renderTerm' False ctx x : infixTerms str xs 
        infixTerms str args | (first, rest) <- span (/='_') str = constant first : infixTerms rest args

    freevar v = inline "freevar" (name v)
    metavar v r = inline "metavar" (name ('?':v) ++ r)
    constant v = inline "const" (name v)
    boundName txt = inline "boundName" (name txt)
    binder txt bdy = inline "binder" $ [boundName txt, text ".", space, bdy]

    renderITelescope ts = []

    peelApTelescope' t | (t', args) <- peelApTelescope t 
                       = case t' of 
                           MetaVar i | not (showTeles opts)
                                     -> let (args1, args2) = span isAtom args
                                         in (MetaVar i, args1, args2)
                           _ -> (t',[],args)
      where isAtom (LocalVar _) = True
            isAtom _ = False

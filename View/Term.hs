{-# LANGUAGE OverloadedStrings #-}
module View.Term where
import Miso
import Terms
import DisplayOptions
import View.Utils
import Data.List (intersperse)
import qualified Miso.String as MS
renderTerm opts trm = renderTermCtx [] opts trm

renderTermCtx :: [Name] -> TermDisplayOptions -> Term -> View a
renderTermCtx context opts trm = noActionsCoerce $ (renderTermCtxEditable Nothing context opts trm :: View (LocalAction Bool Bool))

renderTermCtxEditable :: (Eq focus, Eq action) 
                      => Maybe (MS.MisoString, Int -> focus, Int -> action, Maybe focus) 
                      -> [Name] -> TermDisplayOptions -> Term -> View (LocalAction focus action)
renderTermCtxEditable editable context opts trm = renderTerm' True context trm
  where
    renderTerm' outer ctx (Lam (M v) t) = binder v (renderTerm' True (v : ctx) t)
    renderTerm' outer ctx other = renderTerm'' outer ctx other
    renderTerm'' outer ctx t
      | Lam _ _ <- t = multi $ parenthesise [renderTerm' False ctx t]
      | (x, ts, []) <- peelApTelescope' t = case x of
        LocalVar j
          | j >= length ctx -> boundName (MS.pack $ show j)
          | length ctx - j <= length context -> freevar (ctx !! j)
          | otherwise -> boundName (ctx !! j)
        MetaVar i -> case editable of 
          Nothing -> metavar i
          Just (textIn, focus, act, selected) -> editableMath textIn (metavar i) (focus i) (act i) [] selected
        Const s -> constant s

      | (Const n, [], args) <- peelApTelescope' t
      , showInfixes opts
      , MS.count "_" n == length args
      = multi $ (if outer then id else parenthesise) $ intersperse space (infixTerms n args)

      | (x, ts, args) <- peelApTelescope' t
      = multi $ (if outer then id else parenthesise) $
          renderTerm'' False ctx x : space : intersperse space (map (renderTerm'' False ctx) args)
      where
        infixTerms str [] | MS.null str = []
        infixTerms str [] = [constant str]
        infixTerms str (x : xs) | Just ('_',str) <- MS.uncons str = renderTerm' False ctx x : infixTerms str xs
        infixTerms str args | (first, rest) <- MS.span (/= '_') str = constant first : infixTerms rest args

    freevar v = inline "term-freevar" (name v)
    metavar v = inline "term-metavar" (name $ MS.pack ('?' : show v))
    constant v = inline "term-const" (name v)
    boundName txt = inline "term-bound" (name txt)
    binder txt bdy = inline "term-binder" $ [boundName txt, ".", space, bdy]

    peelApTelescope' t | (t', args) <- peelApTelescope t =
      case t' of
        MetaVar i
          | not (showTeles opts) ->
            let (args1, args2) = span isAtom args
             in (MetaVar i, args1, args2)
        _ -> (t', [], args)
      where
        isAtom (LocalVar _) = True
        isAtom _ = False

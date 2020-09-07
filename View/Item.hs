module View.Item where

import qualified Editor as E
import qualified Item as I
import View.Utils
import View.Heading
import View.Rule
import View.Paragraph

toGlobalAction :: Int -> LocalAction (I.Focus I.Item) (I.Action I.Item) -> E.EditorAction
toGlobalAction _ (UpdateInput s) = E.UpdateInput s
toGlobalAction _ Reset = E.Reset
toGlobalAction i (Act a) = E.ItemAction (Just i) a
toGlobalAction i (SetFocus f) = E.SetFocus (E.ItemFocus i f)

mapLocalAction :: (a -> a')-> (b -> b') -> LocalAction a b -> LocalAction a' b'
mapLocalAction f g (UpdateInput s) = UpdateInput s
mapLocalAction f g Reset = Reset
mapLocalAction f g (Act a) = Act (g a)
mapLocalAction f g (SetFocus b) = SetFocus (f b)

toLocalFocus :: Int -> E.EditorFocus -> Maybe (I.Focus I.Item)
toLocalFocus i (E.ItemFocus i' f) | i == i' = Just f 
toLocalFocus _ _ = Nothing


renderItem opts index textIn item focus = case item of 
   I.Paragraph para -> fmap (toGlobalAction index . mapLocalAction I.ParagraphFocus I.ParagraphAct)
                     $ renderParagraph textIn (fmap (\(I.ParagraphFocus p) -> p) $ toLocalFocus index focus) para
   I.Heading   head -> fmap (toGlobalAction index . mapLocalAction I.HeadingFocus I.HeadingAct)
                     $ renderHeading index textIn (fmap (\(I.HeadingFocus p) -> p) $ toLocalFocus index focus) head
   I.Rule      rule -> fmap (toGlobalAction index . mapLocalAction I.RuleFocus I.RuleAct)
                     $ renderRule index opts textIn (fmap (\(I.RuleFocus p) -> p) $ toLocalFocus index focus) rule


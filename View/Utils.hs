{-# LANGUAGE OverloadedStrings #-}
module View.Utils where
import Miso
import qualified Miso.String as MS
import Data.Char
import Data.List (dropWhileEnd, intersperse)
import Data.Maybe (fromMaybe)

data LocalAction f a = UpdateInput MS.MisoString | Reset | Act a | SetFocus f deriving (Show, Eq)

mapLocalAction :: (a -> a') -> (b -> b') -> LocalAction a b -> LocalAction a' b'
mapLocalAction f g (UpdateInput s) = UpdateInput s
mapLocalAction f g Reset = Reset
mapLocalAction f g (Act a) = Act (g a)
mapLocalAction f g (SetFocus b) = SetFocus (f b)

noActionsCoerce :: View a -> View b 
noActionsCoerce = fmap (const $ error "Actions triggered on a noActionsCoerce node!")

block cls is = div_ [class_ cls] is
inline cls is = span_ [class_ cls] is
multi = span_ []
anchor i = a_ [id_ $ "anchor" <> MS.pack (show i)]

metabinder v = inline "rule-binder" (name v ++ ["."])

axiomHeading i = block "item-rule-theoremheading" [anchor i ["Axiom."]]
inductionHeading i = block "item-rule-theoremheading" [h3_ [] [anchor i ["Induction Axioms."]]]
basisSubheading i = block "item-rule-theoremheading" [anchor i ["Basis."]]
stepsSubheading i = block "item-rule-theoremheading" [anchor i ["Inductive Steps."]]
princSubheading i = block "item-rule-theoremheading" [anchor i ["Inductive Principle."]]
theoremHeading i = block "item-rule-theoremheading" [anchor i ["Theorem."]]

space = inline "space" [" "]
turnstile = inline "symbol symbol-turnstile symbol-bold" ["⊢"]
miniTurnstile = sub_ [class_ "symbol-mini"] ["⊢"]
comma = inline "symbol symbol-bold symbol-comma" [","]
placeholder = inline "placeholder" ["␣"]

localrule i = inline "rule-rulename-local" [text (MS.pack (show i))]
definedrule d = inline "rule-rulename-defined" (name d)

button cls title onClk 
  | MS.null title = button_ [class_ cls, type_ "button", onClick onClk]
  | otherwise     = button_ [class_ cls, type_ "button", title_ title, onClick onClk]

submitButton cls title = button_ [class_ cls, title_ title]
focusedButton cls title onClk content =
  multi
    [ button_ [class_ cls, title_ title, type_ "button", id_ "focusedButton", onClick onClk] content
    , script_ [] "document.getElementById('focusedButton').focus();"
    ]

iconButton typ title icn act = button ("button-icon button-icon-" <> typ) title act [typicon icn] 

focusHack i = script_ []
  $  "document.getElementById('" <> i <> "').focus();"
  <> "document.getElementById('" <> i <> "').select();"

typicon icn = inline ("typcn typcn-" <> icn) []

labelledBrackets content label = multi 
  [ inline "symbol symbol-bold" ["⟨"]
  , content
  , inline "symbol symbol-bold" ["⟩"], sup_ [] [label]
  ]

parenthesise = ([inline "symbol" ["("]] ++) . (++ [inline "symbol" [")"]])

textbox i act n = input_ [id_ i, onChange act, value_ n]
expandingTextbox i act n 
  = multi
    [ input_ [id_ i, class_ $ "expandingTextbox-" <> i, onChange act, value_ n]
    , script_ [] 
      $ "its = document.getElementsByClassName('expandingTextbox-" <> i <>"');"
      <> "var fn = function(evt) { for (it of its) {"
      <>   "it.style.width='';it.value = evt.target.value;it.style.width = it.scrollWidth+'px';"
      <> "}};"
      <> "for (it of its) {" 
      <>   "it.addEventListener('input',fn);it.style.width='';it.style.width = it.scrollWidth+'px';"
      <> "}"
    ]

expandingTextarea ids cls act textIn =
  multi
    [ textarea_ [id_ ids, onChange act, class_ cls] [text textIn]
    , script_ []
      $  "it = document.getElementById('ta');"
      <> "var fn = function() {"
      <> "it.style.height=''; it.style.height = it.scrollHeight+'px'; "
      <> "}; window.setTimeout(fn,100); it.addEventListener('input',fn);"
      <> "it.focus();it.setSelectionRange(it.value.length, it.value.length);"
    ]

inferrule binders premises spacer ruleTitle conclusion =
  table_
    [  intProp "cellpadding" 0, class_ "inference",intProp "cellspacing" 0]
    [ tr_ []
      $  [td_ [class_ "rule-cell rule-binderbox", rowspan_ "2"] binders]
      ++ map (td_ [class_ "rule-cell rule-premise"] . pure) premises
      ++ [td_ [class_ "rule-cell rule-spacer"] [spacer]]
      ++ [td_ [rowspan_ "2", class_ "rule-cell rule-rulebox"] [fromMaybe "" ruleTitle]]
    , tr_ [] [td_ [class_ "rule-cell rule-conclusion", colspan_ (MS.pack $ show $ length premises + 1)] conclusion]
    ]

hypothetical showTurnstile binders premises spacer ruleTitle conclusion =
  table_
    [intProp "cellpadding" 0, intProp "cellspacing" 0]
    [ tr_ [] 
      $  [td_ [class_ "rule-cell rule-binderbox", rowspan_ "3"] binders]
      ++ map (td_ [class_ "rule-cell rule-premise"] . pure) premises
      ++ [td_ [class_ "rule-cell rule-spacer"] [spacer]]
      ++ [td_ [rowspan_ "3", class_ "rule-cell rule-rulebox"] [fromMaybe "" ruleTitle]]
    , tr_ [] 
      [ td_ [class_ "rule-cell", colspan_ (MS.pack $ show $ length premises + 1)] 
      $ if not (null premises) || showTurnstile then ["⋮"] else []
      ]
    , tr_ [] [td_ [class_ "rule-cell rule-hypothetical-conclusion", colspan_ (MS.pack $ show $ length premises + 1)] conclusion]
    ]

entailment showTurnstile binders premises spacer ruleTitle conclusion =
  multi $ maybe [] (:":":space:[]) ruleTitle 
    ++ binders
    ++ [ wrap (intersperse comma premises ++ [spacer])
       , if not (null premises) || showTurnstile then turnstile else ""
       ]
    ++ conclusion
  where
    wrap [] = multi []
    wrap xs = inline "rule-context" xs

editor typ act = editor' typ (Act act) UpdateInput Reset

editor' typ act update reset n =
  form_
    [class_ $ "editor editor-" <> typ, onSubmit act]
    [ (if typ `elem` ["expanding", "newrule"] then expandingTextbox else textbox) "editor-textbox" update n
    , submitButton "button-icon button-icon-blue" "Confirm" [typicon "tick-outline"]
    , iconButton "grey" "Cancel" "times-outline" reset 
    , focusHack "editor-textbox"
    ]

editorWithTitle title typ act update reset n =
  form_
    [class_ $ "editor editor-" <> typ, onSubmit act]
    [ title
    , (if typ == "expanding" then expandingTextbox else textbox) "editor-textbox" update n
    , submitButton "button-icon button-icon-blue" "Confirm" [typicon "tick-outline"]
    , iconButton "grey" "Cancel" "times-outline" reset
    , focusHack "editor-textbox"
    ]

editableMath text view focus act extraActions selected
  | selected == Just focus = if null extraActions then ed else multi (ed : extraActions)
  | otherwise = button "editable editable-math" "" (SetFocus focus) [view]
  where
    ed = editor "expanding" act text

name str = concatMap go (MS.words str)
  where go str = concat $ intersperse [placeholder] (map name' (MS.splitOn "_" str))
name' s =
  let noPrimes = MS.dropWhileEnd (== '\'') s
      bulk = MS.dropWhileEnd (isDigit) noPrimes
      rest = MS.drop (MS.length bulk) noPrimes
      bulk' = case bulk of
        "/\\" -> "∧"
        "\\/" -> "∨"
        "not" -> "¬"
        "->" -> "→"
        "<-" -> "←"
        "<->" -> "↔"
        "-->" -> "⟶"
        "<--" -> "⟵ "
        "<-->" -> "⟷"
        "=>" -> "⇒"
        "<==" -> "⇐"
        "<=>" -> "⇔"
        "<==>" -> "⟺"
        "==>" -> "⟹"
        "<===" -> "⟸"
        "<-|" -> "↤"
        "==" -> "≡"
        "lub" -> "⊓"
        "glb" -> "⊔"
        "~=" -> "≃"
        "~" -> "∼"
        "all" -> "∀"
        "exists" -> "∃"
        ":=" -> "≔"
        "times" -> "×"
        "bot" -> "⊥"
        "top" -> "⊤"
        "infinity" -> "∞"
        "[[" -> "〚"
        "]]" -> "〛"
        "[<" -> "〈"
        ">]" -> "〉"
        ">>]" -> "》"
        "[<<" -> "《"
        "<=" -> "≤"
        ">=" -> "≥"
        "/=" -> "≠"
        "|->" -> "↦"
        "nat" -> "ℕ"
        "rational" -> "ℚ"
        "int" -> "ℤ"
        "real" -> "ℝ"
        "bool" -> "𝔹"
        "product" -> "∏"
        "coproduct" -> "∐"
        "sum" -> "∑"
        "union" -> "∪"
        "intersection" -> "∩"
        "subseteq" -> "⊆"
        "supseteq" -> "⊇"
        "subset" -> "⊂"
        "supset" -> "⊃"
        "elem" -> "∈"
        "eval" -> "⇓"
        "alpha" -> "α"
        "beta" -> "β"
        "gamma" -> "γ"
        "delta" -> "δ"
        "epsilon" -> "ε"
        "zeta" -> "ζ"
        "eta" -> "η"
        "theta" -> "θ"
        "iota" -> "ι"
        "kappa" -> "κ"
        "lambda" -> "λ"
        "varepsilon" -> "ϵ"
        "mu" -> "μ"
        "nu" -> "ν"
        "xi" -> "ξ"
        "pi" -> "π"
        "rho" -> "ρ"
        "sigma" -> "σ"
        "varsigma" -> "ς"
        "tau" -> "τ"
        "phi" -> "φ"
        "psi" -> "ψ"
        "chi" -> "χ"
        "omega" -> "ω"
        "upsilon" -> "υ"
        "Gamma" -> "Γ"
        "Delta" -> "Δ"
        "Theta" -> "Θ"
        "Lambda" -> "Λ"
        "Xi" -> "Ξ"
        "Pi" -> "Π"
        "Sigma" -> "Σ"
        "Phi" -> "Φ"
        "Psi" -> "Ψ"
        "Omega" -> "Ω"
        _ -> bulk
      primeString = makePrimeString (MS.length s - MS.length noPrimes)
      makePrimeString 0 = ""
      makePrimeString 1 = "′"
      makePrimeString 2 = "″"
      makePrimeString 3 = "‴"
      makePrimeString 4 = "⁗"
      makePrimeString n = "⁗" <> makePrimeString (n - 4)
   in if MS.null bulk' then [text rest] else [text bulk', sub_ [] [text rest], text primeString]
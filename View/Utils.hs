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


block cls is = div_ [class_ cls] is
inline cls is = span_ [class_ cls] is
multi = span_ []
anchor i = a_ [id_ $ "anchor" <> MS.pack (show i)]

metabinder v = inline "rule-binder" (name v ++ ["."])

axiomHeading i = block "item-rule-theoremheading" [anchor i ["Axiom."]]
theoremHeading i = block "item-rule-theoremheading" [anchor i ["Theorem."]]


space = inline "space" [" "]
turnstile = inline "symbol symbol-turnstile symbol-bold" ["⊢"]
miniTurnstile = sub_ [class_ "symbol-mini"] ["⊢"]
comma = inline "symbol symbol-bold symbol-comma" [","]
placeholder = inline "placeholder" ["␣"]

localrule i = inline "rule-rulename-local" [text (MS.pack (show i))]
definedrule d = inline "rule-rulename-defined" (name d)

button cls onClk = button_ [class_ cls, type_ "button", onClick onClk]
submitButton cls = button_ [class_ cls]
focusedButton cls onClk content =
  multi
    [ button_ [class_ cls, type_ "button", id_ "focusedButton", onClick onClk] content
    , script_ [] "document.getElementById('focusedButton').focus();"
    ]

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

textbox i act n = input_ [id_ i, onInput act, value_ n]
expandingTextbox i act n = input_ [id_ i, style_ ("width" =: MS.pack (show size <> "em")), onInput act, value_ n]
  where size = ((fromIntegral (MS.length n) + 1) * 16) / 30

expandingTextarea ids cls act textIn =
  multi
    [ textarea_ [id_ ids, onInput act, class_ cls] [text textIn]
    , script_ []
      $  "it = document.getElementById('ta');"
      <> "var fn = function() {"
      <> "it.style.height=''; it.style.height = it.scrollHeight+'px'; "
      <> "}; window.setTimeout(fn,100); it.addEventListener('input',fn);"
      <> "it.focus();it.setSelectionRange(it.value.length, it.value.length);"
    ]

inferrule binders premises spacer ruleTitle conclusion =
  table_
    [intProp "cellpadding" 0, intProp "cellspacing" 0]
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
    , submitButton "button-icon button-icon-blue" [typicon "tick-outline"]
    , button "button-icon button-icon-grey" reset [typicon "times-outline"]
    , focusHack "editor-textbox"
    ]

editorWithTitle title typ act update reset n =
  form_
    [class_ $ "editor editor-" <> typ, onSubmit act]
    [ title
    , (if typ == "expanding" then expandingTextbox else textbox) "editor-textbox" update n
    , submitButton "button-icon button-icon-blue" [typicon "tick-outline"]
    , button "button-icon button-icon-grey" reset [typicon "times-outline"]
    , focusHack "editor-textbox"
    ]

editableMath text view focus act extraActions selected
  | selected == Just focus = if null extraActions then ed else multi (ed : extraActions)
  | otherwise = button "editable editable-math" (SetFocus focus) [view]
  where
    ed = editor "expanding" act text

name [] = []
name ('_' : str) = placeholder : name str
name (' ' : str) = name str
name str | (first, rest) <- span (`notElem` ("_ " :: [Char])) str = name' first ++ name rest
name' s =
  let noPrimes = dropWhileEnd (== '\'') s
      bulk = dropWhileEnd (isDigit) noPrimes
      rest = drop (length bulk) noPrimes
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
      primeString = makePrimeString (length s - length noPrimes)
      makePrimeString 0 = ""
      makePrimeString 1 = "′"
      makePrimeString 2 = "″"
      makePrimeString 3 = "‴"
      makePrimeString 4 = "⁗"
      makePrimeString n = "⁗" <> makePrimeString (n - 4)
   in if bulk' == "" then [text (MS.pack rest)] else [text (MS.pack bulk'), sub_ [] [text (MS.pack rest)], text primeString]
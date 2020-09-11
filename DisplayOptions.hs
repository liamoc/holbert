module DisplayOptions where 
    
data DisplayOptions = O 
  { showMetaBinders :: Bool
  , assumptionsMode :: AssumptionsMode
  , compactRules    :: RuleStyle
  , tDOs            :: TermDisplayOptions
  } deriving (Show, Eq)

data TermDisplayOptions = TDO {showTeles :: Bool, showInfixes :: Bool}
  deriving (Show, Eq)

data RuleStyle = BarTurnstile | Turnstile | Bar | Dots 
  deriving (Show, Eq)

data AssumptionsMode = Cumulative | New | Hidden
  deriving (Show, Eq)
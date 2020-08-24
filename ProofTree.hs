module ProofTree where 
import Control.Monad
import Unification
import Terms
import Data.Maybe
import Data.List
import Debug.Trace
import StringRep
import Prop

data ProofTree = Goal ([String]) ([Prop]) Term 
               | Rule RuleRef ([String]) ([Prop]) Term ([ProofTree]) deriving (Eq, Show)

data ProofTreeContext = PTC  RuleRef ([String]) ([Prop]) Term ([ProofTree]) ([ProofTree]) deriving (Eq, Show)

data Zipper = Zip Path ([ProofTreeContext]) ProofTree deriving (Eq, Show)


allSkolems :: ProofTree -> [String]
allSkolems (Goal sks _ _) = sks
allSkolems (Rule _ sks _ _ pts) = sks ++ concatMap allSkolems pts

up :: Zipper -> Maybe Zipper 
up (Zip pth ctx (Rule r skms lrs g (sg: sgs))) = Just (Zip (0:pth) (PTC r skms lrs g [] sgs:ctx) sg)
up _ = Nothing

down :: Zipper -> Maybe Zipper 
down (Zip (_ :pth) ((PTC r skms lrs g lefts rights): ctx) sg) = Just (Zip pth ctx (Rule r skms lrs g (lefts ++ sg:rights)))
down _ = Nothing

left :: Zipper -> Maybe Zipper
left (Zip pth ((PTC r skms lrs g (lg: lefts) rights): ctx) sg) = Just (Zip pth (PTC r skms lrs g lefts (sg:rights): ctx) lg)
left _ = Nothing

right :: Zipper -> Maybe Zipper
right (Zip pth (PTC r skms lrs g lefts (rg: rights): ctx) sg) = Just (Zip pth ((PTC r skms lrs g (sg:lefts) rights): ctx) rg)
right _ = Nothing

substRRPT :: String -> String -> ProofTree -> ProofTree
substRRPT new old (Rule rr sks lcls trm pts) = Rule (if rr == Defn old then Defn new else rr) sks lcls trm (map (substRRPT new old) pts)
substRRPT new old r = r 

renameMeta :: (Path, Int) -> String -> ProofTree -> ProofTree
renameMeta (p,x) s pt = do
   let z = path' p (Zip [] [] pt) 
       z' = renameMetaZ x s z
    in unwind z'

renameMetaZ :: Int -> String -> Zipper -> Zipper
renameMetaZ x s (Zip pth ctx g) = Zip pth ctx $ case g of
         (Rule rr sks lcls trm pts) ->
           let sks' = modifyAt x (\_ -> s) sks
            in  Rule rr sks' lcls trm pts
         (Goal sks lcls trm) ->
           let sks' = modifyAt x (\_ -> s) sks
            in Goal sks' lcls trm

upRightN :: Int -> Zipper -> Maybe Zipper 
upRightN 0 = up
upRightN n = right <=< upRightN (n-1)

path :: Path -> Zipper -> Maybe Zipper 
path = foldr (\n f -> upRightN n <=< f) Just

validPath :: Path -> ProofTree -> Bool
validPath p pt = not $ isNothing $ path p $ Zip [] [] pt
path' :: Path -> Zipper -> Zipper 
path' p z = fromMaybe z (path p z)
rewind :: Zipper -> Zipper 
rewind z = maybe z rewind (down z)
unwind :: Zipper -> ProofTree 
unwind z = let Zip _ _ pt = rewind z in pt 
nixFrom :: Path -> ProofTree -> ProofTree
nixFrom p pt = let (Zip pth ctx (Rule rr sks lcls g sgs)) = path' p (Zip [] [] pt)
               in unwind (Zip pth ctx (Goal sks lcls g))

doRule :: (RuleRef, Prop) -> Path -> ProofTree -> Gen (Maybe ProofTree)
doRule r p pt = do
   let z = path' p (Zip [] [] pt) 
   mb <- rule r z
   pure $ fmap unwind $ mb

queryAtPath :: Path -> (Zipper -> a) -> ProofTree -> a
queryAtPath p f pt = f (path' p (Zip [] [] pt))

substMVZ :: Subst -> Zipper -> Zipper 
substMVZ sbst (Zip pth ctx pt) = (Zip pth (map (substMVC sbst) ctx) (substMVPT sbst pt))
  where 
    substMVC subst (PTC rr sks lcls g ls rs) =
       (PTC rr sks (map (substMVP subst) lcls) (substG subst g) (map (substMVPT subst) ls) (map (substMVPT subst) rs)) 
    substMVP subst (Forall vs lcls g) = Forall vs (map (substMVP subst) lcls) (substG subst g)
    substG subst g = reduce (applySubst subst g)
    substMVPT subst (Rule rr sks lcls g sgs) = 
        (Rule rr sks (map (substMVP subst) lcls) (substG subst g) (map (substMVPT subst) sgs))
    substMVPT subst (Goal sks lcls g) = 
        (Goal sks (map (substMVP subst) lcls) (substG subst g))

rule :: (RuleRef, Prop) -> Zipper -> Gen (Maybe Zipper)
rule (r,rl) z@(Zip pth ctx (Goal sks lcls g)) = do
        ms <- applyRule (knownSkolems z) g rl 
        case ms of 
            Nothing -> pure Nothing 
            Just (sbst, sgs) -> do 
               pure (Just (substMVZ sbst (Zip pth ctx (Rule r sks lcls g sgs))))
rule r _ = pure Nothing 

knownLocals :: Zipper -> [Prop]
knownLocals (Zip _ ctx (Goal sks lcls _))= map (raiseProp 0 (length sks)) (contextLocals ctx) ++ lcls
knownLocals (Zip _ ctx (Rule _ sks lcls _ _)) = map (raiseProp 0 (length sks)) (contextLocals ctx) ++ lcls

contextLocals :: [ProofTreeContext] -> [Prop]
contextLocals [] = []
contextLocals (c@(PTC _ sks lcls _ _ _):rest) = let acc = contextLocals rest
                                                 in map (raiseProp 0 (length sks)) acc ++ lcls

knownSkolems :: Zipper -> [String]
knownSkolems (Zip _ ctx (Goal sks _ _)) = reverse sks ++ concatMap (\(PTC _ sks _ _ _ _) -> reverse sks) ctx 
knownSkolems (Zip _ ctx (Rule _ sks _ _ _)) = reverse sks ++ concatMap (\(PTC _ sks _ _ _ _) -> reverse sks) ctx

fromProp :: Prop -> ProofTree
fromProp (Forall sks lcls g) = Goal sks lcls g


applyRule :: [String] -> Term -> Prop -> Gen (Maybe (Subst, [ProofTree]))
applyRule skolems g (Forall (m :ms) sgs g') = do 
   n <- MetaVar . show <$> gen 
   let mt = foldl Ap n (map LocalVar [0..length skolems -1]) 
   applyRule skolems g (substProp mt 0 (Forall ms sgs g'))
applyRule skolems g (Forall [] sgs g') 
   = do msubst <- unifier g g' 
        pure $ case msubst of 
          Just subst -> Just (subst, map fromProp sgs)
          Nothing -> Nothing


  

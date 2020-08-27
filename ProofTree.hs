module ProofTree where 
import Control.Monad
import Unification
import Data.Maybe
import Data.List
import Debug.Trace
import StringRep
import qualified Prop as P
import qualified Terms as T

modifyAtE :: Int -> (a -> Either e a) -> [a] -> Either e [a]
modifyAtE i f xs 
  = let (lefts, r:rights) = splitAt i xs
     in (lefts ++) . (:rights) <$> f r

modifyAt' :: Int -> (a -> (a, b)) -> [a] -> ([a], b)
modifyAt' i f xs 
  = let (lefts, r:rights) = splitAt i xs
        (r',b) = f r
     in (lefts ++ r':rights, b)

modifyAtMany :: Int -> (a -> [a]) -> [a] -> [a]
modifyAtMany i f xs 
  = let (lefts, r:rights) = splitAt i xs
     in lefts ++ (f r ++ rights)
modifyAt :: Int -> (a -> a) -> [a] -> [a]
modifyAt i f xs 
  = let (lefts, r:rights) = splitAt i xs
     in lefts ++ (f r:rights)

data RuleRef = Defn String | Local Int deriving (Eq, Show)
data ProofTree = PT [T.Id] [P.Prop] T.Term (Maybe (RuleRef, [ProofTree])) deriving (Eq, Show)
type Path = [Int]

data ProofTreeContext = PTC  RuleRef [T.Id] [P.Prop] T.Term [ProofTree] [ProofTree] deriving (Eq, Show)

data Zipper = Zip Path [ProofTreeContext] ProofTree deriving (Eq, Show)

allSkolems :: ProofTree -> [String]
allSkolems (PT sks _ _ rst) = sks ++ maybe [] (concatMap allSkolems . snd) rst

up :: Zipper -> Maybe Zipper 
up (Zip pth ctx (PT skms lrs g (Just (r, sg:sgs)))) = Just (Zip (0:pth) (PTC r skms lrs g [] sgs:ctx) sg)
up _ = Nothing

down :: Zipper -> Maybe Zipper 
down (Zip (_ :pth) ((PTC r skms lrs g lefts rights): ctx) sg) = Just (Zip pth ctx (PT skms lrs g $ Just (r, lefts ++ sg:rights)))
down _ = Nothing

left :: Zipper -> Maybe Zipper
left (Zip pth ((PTC r skms lrs g (lg: lefts) rights): ctx) sg) = Just (Zip pth (PTC r skms lrs g lefts (sg:rights): ctx) lg)
left _ = Nothing

right :: Zipper -> Maybe Zipper
right (Zip pth (PTC r skms lrs g lefts (rg: rights): ctx) sg) = Just (Zip pth ((PTC r skms lrs g (sg:lefts) rights): ctx) rg)
right _ = Nothing

substRRPT :: String -> String -> ProofTree -> ProofTree
substRRPT new old (PT sks lcls trm (Just (rr,pts))) 
  = PT  sks lcls trm (Just (if rr == Defn old then Defn new else rr, map (substRRPT new old) pts))
substRRPT new old r = r 

renameMeta :: (Path, Int) -> String -> ProofTree -> ProofTree
renameMeta (p,x) s pt = do
   let z = path' p (Zip [] [] pt) 
       z' = renameMetaZ x s z
    in unwind z'

renameMetaZ :: Int -> String -> Zipper -> Zipper
renameMetaZ x s (Zip pth ctx g) = Zip pth ctx $ case g of
         (PT sks lcls trm pts) ->
           let sks' = modifyAt x (\_ -> s) sks
            in  PT sks' lcls trm pts

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
nixFrom p pt = let (Zip pth ctx (PT sks lcls g _)) = path' p (Zip [] [] pt)
               in unwind (Zip pth ctx (PT sks lcls g Nothing))

doRule :: (RuleRef, P.Prop) -> Path -> ProofTree -> Gen (Maybe ProofTree)
doRule r p pt = do
   let z = path' p (Zip [] [] pt) 
   mb <- rule r z
   pure $ fmap unwind $ mb

queryAtPath :: Path -> (Zipper -> a) -> ProofTree -> a
queryAtPath p f pt = f (path' p (Zip [] [] pt))

substMVZ :: T.Subst -> Zipper -> Zipper 
substMVZ sbst (Zip pth ctx pt) = (Zip pth (map (substMVC sbst) ctx) (substMVPT sbst pt))
  where 
    substMVC subst (PTC rr sks lcls g ls rs) =
       (PTC rr sks (map (substMVP subst) lcls) (substG subst g) (map (substMVPT subst) ls) (map (substMVPT subst) rs)) 
    substMVP subst (P.Forall vs lcls g) = P.Forall vs (map (substMVP subst) lcls) (substG subst g) -- TODO move to prop
    substG subst g = T.reduce (T.applySubst subst g)
    substMVPT subst (PT sks lcls g sgs) = 
        PT sks (map (substMVP subst) lcls) (substG subst g) (fmap (fmap (map (substMVPT subst))) sgs)

rule :: (RuleRef, P.Prop) -> Zipper -> Gen (Maybe Zipper)
rule (r,rl) z@(Zip pth ctx (PT sks lcls g Nothing)) = do
        ms <- applyRule (knownSkolems z) g rl 
        case ms of 
            Nothing -> pure Nothing 
            Just (sbst, sgs) -> do 
               pure (Just (substMVZ sbst (Zip pth ctx (PT sks lcls g (Just (r,sgs))))))
rule r _ = pure Nothing 

knownLocals :: Zipper -> [P.Prop]
knownLocals (Zip _ ctx (PT sks lcls _ _)) = map (P.raise (length sks)) (contextLocals ctx) ++ lcls

contextLocals :: [ProofTreeContext] -> [P.Prop]
contextLocals [] = []
contextLocals (c@(PTC _ sks lcls _ _ _):rest) = let acc = contextLocals rest
                                                 in map (P.raise (length sks)) acc ++ lcls

knownSkolems :: Zipper -> [String]
knownSkolems (Zip _ ctx (PT sks _ _ _)) = reverse sks ++ concatMap (\(PTC _ sks _ _ _ _) -> reverse sks) ctx

fromProp :: P.Prop -> ProofTree
fromProp (P.Forall sks lcls g) = PT sks lcls g Nothing


applyRule :: [String] -> T.Term -> P.Prop -> Gen (Maybe (T.Subst, [ProofTree]))
applyRule skolems g (P.Forall (m :ms) sgs g') = do 
   n <- T.MetaVar . show <$> gen 
   let mt = foldl T.Ap n (map T.LocalVar [0..length skolems -1]) 
   applyRule skolems g (P.subst mt 0 (P.Forall ms sgs g'))
applyRule skolems g (P.Forall [] sgs g') 
   = do msubst <- unifier g g' 
        pure $ case msubst of 
          Just subst -> Just (subst, map fromProp sgs)
          Nothing -> Nothing


  

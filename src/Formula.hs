
{-# LANGUAGE LambdaCase #-}

module Formula (
    Term (..),
    Formula (..),
    nnf,
    miniscope,
    sort,
    convertScope,
    rename,
    purify
) where

import qualified Data.List as L
import Data.Char
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M

import Debug.Trace

data Term =
    Constant String
    | Variable String
    | Function String [Term]
    deriving (Eq, Ord)

instance Show Term where
    show (Constant n) = L.map toUpper n
    show (Variable n) = L.map toLower n
    show (Function n ts) =
        L.map toLower n ++ "(" ++ L.intercalate ", " (L.map show ts) ++ ")"

data Formula =
    -- Literals
    T
    | F
    | Pred String [Term]
    | Not Formula
    -- Binary connectives
    | And Formula Formula
    | Or Formula Formula
    | Impl Formula Formula
    | Iff Formula Formula
    -- Quantifiers
    | Exists Term Formula
    | All Term Formula
    deriving (Eq, Ord)

isAnd :: Formula -> Bool
isAnd (And _ _) = True
isAnd _ = False

isOr :: Formula -> Bool
isOr (Or _ _) = True
isOr _ = False

map :: (Formula -> Formula) -> Formula -> Formula
map f = \case
    Not a -> Not (f a)
    And a b -> And (f a) (f b)
    Or a b -> Or (f a) (f b)
    Impl a b -> Impl (f a) (f b)
    Iff a b -> Iff (f a) (f b)
    Exists t a -> Exists t (f a)
    All t a -> All t (f a)
    a -> a

instance Show Formula where
    show = \case
        T -> "⊤"
        F -> "⊥"
        Pred n ts ->
            L.map toUpper n ++ L.intercalate "" (L.map show ts)
        Not f' ->
            "!" ++ "(" ++ show f' ++ ")"
        And fa fb ->
            "(" ++ show fa ++ " ∧ " ++ show fb ++ ")"
        Or fa fb ->
            "(" ++ show fa ++ " ∨ " ++ show fb ++ ")"
        Impl fa fb ->
            show fa ++ " -> " ++ show fb
        Iff fa fb ->
            show fa ++ " <-> " ++ show fb
        Exists t f' ->
            "E" ++ show t ++ ". (" ++ show f' ++ ")"
        All t f' ->
            "A" ++ show t ++ ". (" ++ show f' ++ ")"

vars :: Formula -> S.Set Term
vars f =
    vars' f S.empty
    where
        folder s v@(Variable _) = S.insert v s
        folder s _ = s

        vars' (Pred _ ts) s = foldl folder s ts
        vars' (Not f') s = vars' f' s
        vars' (And fa fb) s = S.union (vars' fa s) (vars' fb s)
        vars' (Or fa fb) s = S.union (vars' fa s) (vars' fb s)
        vars' (Impl fa fb) s = S.union (vars' fa s) (vars' fb s)
        vars' (Iff fa fb) s = S.union (vars' fa s) (vars' fb s)
        vars' (Exists _ f') s = vars' f' s
        vars' (All _ f') s = vars' f' s
        vars' _ s = s

bound :: Formula -> S.Set Term
bound f =
    bound' f S.empty
    where
        bound' (Exists t f') s = S.insert t (bound' f' s)
        bound' (All t f') s = S.insert t (bound' f' s)
        bound' (Not f') s = bound' f' s
        bound' (And fa fb) s = S.union (bound' fa s) (bound' fb s)
        bound' (Or fa fb) s = S.union (bound' fa s) (bound' fb s)
        bound' (Impl fa fb) s = S.union (bound' fa s) (bound' fb s)
        bound' (Iff fa fb) s = S.union (bound' fa s) (bound' fb s)
        bound' _ s = s

free :: Formula -> S.Set Term
free f = S.difference (vars f) (bound f)

binds :: Formula -> Term -> Bool
binds f t = S.member t (free f)

-- Number of quantifiers in a `Formula`.
numQuantifiers :: Formula -> Int
numQuantifiers T = 0
numQuantifiers F = 0
numQuantifiers (Pred _ _) = 0
numQuantifiers (All _ f) = numQuantifiers f + 1
numQuantifiers (Exists _ f) = numQuantifiers f + 1
numQuantifiers (Not f) = numQuantifiers f
numQuantifiers (And p q) = numQuantifiers p + numQuantifiers q
numQuantifiers (Or p q) = numQuantifiers p + numQuantifiers q
numQuantifiers (Impl p q) = numQuantifiers p + numQuantifiers q
numQuantifiers (Iff p q) = numQuantifiers p + numQuantifiers q

-- Convert a Formula into Negation Normal Form (NNF.)
nnf :: Formula -> Formula
nnf (Not T) = F
nnf (Not F) = T
nnf (Not (Not p)) = nnf p
nnf (Not (And p q)) = Formula.map nnf $ Or (Not p) (Not q)
nnf (Not (Or p q)) = Formula.map nnf $ And (Not p) (Not q)
nnf (Not (Impl p q)) = Formula.map nnf $ And p (Not q)
nnf (Not (Iff p q)) = Formula.map nnf $ Or (And p (Not q)) (And (Not p) q)
nnf (Not (All t p)) = Formula.map nnf $ Exists t (Not p)
nnf (Not (Exists t p)) = Formula.map nnf $ All t (Not p)
nnf p = Formula.map nnf p

{- Purification -}

-- Inverse prenexing, pushes quantifiers inwards as much as possible in one
-- step. (NOT as much as possible in general.)
miniscope :: Formula -> Formula
miniscope (All t p) = pushAll t (miniscope p)
miniscope (Exists t p) = pushExists t (miniscope p)
miniscope p = Formula.map miniscope p

pushExists :: Term -> Formula -> Formula
pushExists t f =
    if push == f then Exists t f else push
    where
    push = case f of
        (Or a b) | a `binds` t && b `binds` t ->
            Or (pushExists t a) (pushExists t b)
        (Or a b) | a `binds` t ->
            Or (pushExists t a) b
        (Or a b) | b `binds` t ->
            Or a (pushExists t b)
        (And a b) | a `binds` t && b `binds` t ->
            f
        (And a b) | a `binds` t ->
            And (pushExists t a) b
        (And a b) | b `binds` t ->
            And a (pushExists t b)
        _ -> f

pushAll :: Term -> Formula -> Formula
pushAll t f =
    if push == f then All t f else push
    where
    push = case f of
        (Or a b) | a `binds` t && b `binds` t ->
            f
        (Or a b) | a `binds` t ->
            Or (pushAll t a) b
        (Or a b) | b `binds` t ->
            Or a (pushAll t b)
        (And a b) | a `binds` t && b `binds` t ->
            And (pushAll t a) (pushAll t b)
        (And a b) | a `binds` t ->
            And (pushAll t a) b
        (And a b) | b `binds` t ->
            And a (pushAll t b)
        _ -> f

-- Groups together universal quantifiers separated by disjunctions and
-- existential quantifiers separated by conjunctions.
partialPrenex :: Formula -> Formula
partialPrenex (Or (All t p) q) = All t (partialPrenex (Or p q))
partialPrenex (Or p (All t q)) = All t (partialPrenex (Or p q))
partialPrenex (And (Exists t p) q) = Exists t (partialPrenex (And p q))
partialPrenex (And p (Exists t q)) = Exists t (partialPrenex (And p q))
partialPrenex p =
    if p' /= p then partialPrenex p' else p'
    where
        p' = Formula.map partialPrenex p

-- TODO(mert): All fresh variables are named $k{n}$. This is not ideal, find a
-- better solution.
freshVariable :: Int -> Term
freshVariable i = Variable (newName i)
    where newName n = "k" ++ show n

mapVariable :: (Term -> Term) -> Formula -> Formula
mapVariable m (Pred s ts) = Pred s (m <$> ts)
mapVariable m (Exists t p) = Exists (m t) (mapVariable m p)
mapVariable m (All t p) = All (m t) (mapVariable m p)
mapVariable m p = Formula.map (mapVariable m) p

replaceVariable :: Term -> Term -> Formula -> Formula
replaceVariable s d = mapVariable (\t -> if t == s then d else t)

-- Renames variables in a formula s.t. no two different quantifiers bind
-- the same variable. Used after a sequence of miniscoping and partial
-- prenexing. (Nonnengart & Weidenbach '01)
rename :: Formula -> Formula
rename f = rename' f 1

rename' :: Formula -> Int -> Formula
rename' f@(Pred _ _) _ = f
rename' (And p q) i = And (rename' p i) (rename' q (i + numQuantifiers p))
rename' (Or p q) i = Or (rename' p i) (rename' q (i + numQuantifiers p))
rename' (Impl p q) i = Impl (rename' p i) (rename' q (i + numQuantifiers p))
rename' (Iff p q) i = Iff (rename' p i) (rename' q (i + numQuantifiers p))
rename' (Not p) i = Not (rename' p i)
rename' (Exists t f') i = Exists fv $ rename' (replaceVariable t fv f') (i + 1)
    where fv = freshVariable i
rename' (All t f') i = All fv $ rename' (replaceVariable t fv f') (i + 1)
    where fv = freshVariable i

-- | Returns the number of immediate disjuncts the given term is in.
inNumDisj :: Formula -> Term -> Int
inNumDisj (Or p q) t = inNumDisj p t + inNumDisj q t
inNumDisj p t = if p `binds` t then 1 else 0

-- | Returns the number of immediate conjuncts the given term is in.
inNumConj :: Formula -> Term -> Int
inNumConj (And p q) t = inNumConj p t + inNumConj q t
inNumConj p t = if p `binds` t then 1 else 0

-- | Deconstructs a sequence of `Exists`s.
type ExistsP = (Term, Int)
deconsExists :: Formula -> ([ExistsP], Formula)
deconsExists (Exists ta (Exists tb p)) =
    let (more, innerFormula) = deconsExists p in
    ([(ta, inNumConj p ta), (tb, inNumConj p tb)] ++ more, innerFormula)
deconsExists (Exists ta p) = ([(ta, inNumConj p ta)], p)
deconsExists f = ([], f)

-- | Reconstructs a `Formula` from the output of `deconsExists`.
reconsExists :: [ExistsP] -> Formula -> Formula
reconsExists ((t, _):ds) p = Exists t (reconsExists ds p)
reconsExists [] p = p

-- | Deconstructs a sequence of `All`s.
type AllP = (Term, Int)
deconsAll :: Formula -> ([AllP], Formula)
deconsAll (All ta (All tb p)) =
    let (more, innerFormula) = deconsAll p in
        ([(ta, inNumDisj p ta), (tb, inNumDisj p tb)] ++ more, innerFormula)
deconsAll (All ta p) = ([(ta, inNumDisj p ta)], p)
deconsAll f = ([], f)

-- | Reconstructs a `Formula` from the output of `deconsAll`.
reconsAll :: [AllP] -> Formula -> Formula
reconsAll ((t, _):ds) p = All t (reconsAll ds p)
reconsAll [] p = p

-- | Deconstructs a disjunction into a list.
type DisjI = (Formula, S.Set Term)
deconsDisj :: Formula -> [DisjI]
deconsDisj (And p q) = deconsDisj p ++ deconsDisj q
deconsDisj p = [(p, vars p)]

-- | Reconstructs a disjunction from a list.
reconsDisj :: [DisjI] -> Formula
reconsDisj ((p, _):is)
    | L.null is = p
    | otherwise = Or p (reconsDisj is)

-- | Deconstructs a conjunction into a list.
type ConjI = (Formula, S.Set Term)
deconsConj :: Formula -> [ConjI]
deconsConj (And p q) = deconsConj p ++ deconsConj q
deconsConj p = [(p, vars p)]

-- | Reconstructs a conjunction from a list.
reconsConj :: [ConjI] -> Formula
reconsConj ((p, _):is)
    | L.null is = p
    | otherwise = And p (reconsConj is)

-- | Prenex sorting + scope sorting.
sort :: Formula -> Formula
sort = sort' . rename . partialPrenex

sort' :: Formula -> Formula
sort' f@(Exists _ (Exists _ _)) =
    reconsExists sortedQuantifierVars (sort sortedP)
    where
        (quantifierVars, p) = deconsExists f
        scopeMap = M.fromList quantifierVars
        scope v = fromMaybe 0 (M.lookup v scopeMap)
        key (_, conjunctVars) = minimum (S.map scope conjunctVars)

        sortedConjuncts = reverse (L.sortOn key (deconsConj p))
        sortedP = if isAnd p then reconsConj sortedConjuncts else p

        sortedQuantifierVars = reverse (L.sortOn snd quantifierVars)
sort' f@(All _ (All _ _)) =
    reconsAll sortedQuantifierVars (sort sortedP)
    where
        (quantifierVars, p) = deconsAll f
        scopeMap = M.fromList quantifierVars
        scope v = fromMaybe 0 (M.lookup v scopeMap)
        key (_, disjunctVars) = minimum (S.map scope disjunctVars)

        sortedDisjuncts = reverse (L.sortOn key (deconsDisj p))
        sortedP = if isOr p then reconsDisj sortedDisjuncts else p

        sortedQuantifierVars = reverse (L.sortOn snd quantifierVars)
sort' f = Formula.map sort' f

cnf :: Formula -> Formula
cnf = \case
    (Or (And p q) z) -> And (cnf $ Or p z) (cnf $ Or q z)
    (Or p (And q z)) -> And (cnf $ Or p q) (cnf $ Or p z)
    f -> Formula.map cnf f

dnf :: Formula -> Formula
dnf = \case
    (And (Or p q) z) -> Or (dnf $ And p z) (dnf $ And q z)
    (And p (Or q z)) -> Or (dnf $ And p q) (dnf $ And p z)
    f -> Formula.map dnf f

-- | Scope conversion.
convertScope :: Formula -> Formula
convertScope f = case f of
    (All t (Or p q)) | p `binds` t && q `binds` t -> Formula.map cnf f
    (Exists t (And p q)) | p `binds` t && q `binds` t -> Formula.map dnf f
    _ -> if f' /= f then convertScope f' else f'
    where
        f' = Formula.map convertScope f

stable :: (Eq a) => (a -> a) -> a -> a
stable f x = if y' == x then y' else stable f y'
    where y' = f x

-- | Purify.
purify :: Formula -> Formula
purify f = rename . dnf $ f'
    where f' = stable (convertScope . miniscope . sort . miniscope . nnf) f

    


{-# LANGUAGE LambdaCase #-}

module Formula (
    Term (..),
    Formula (..),
    nnf,
    miniscope,
    quantifierSort
) where

import qualified Data.List as L
import Data.Char
import qualified Data.Set as S

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
binds f t = S.member t (vars f)

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
miniscope f@(All t (And a b))
        | a `binds` t && b `binds` t = And (All t a) (All t b)
        | a `binds` t = And (All t a) b
        | b `binds` t = And a (All t b)
        | otherwise = f
miniscope f@(Exists t (Or a b))
        | a `binds` t && b `binds` t = Or (Exists t a) (Exists t b)
        | a `binds` t = Or (Exists t a) b
        | b `binds` t = Or a (Exists t b)
        | otherwise = f
miniscope f@(All t (Or a b))
        | a `binds` t && b `binds` t = f
        | a `binds` t = Or (All t a) b
        | b `binds` t = Or a (All t b)
        | otherwise = f
miniscope f@(Exists t (And a b))
        | a `binds` t && b `binds` t = f
        | a `binds` t = And (Exists t a) b
        | b `binds` t = And a (Exists t b)
        | otherwise = f
miniscope (All t f@(Exists _ _)) = miniscope (All t (miniscope f))
miniscope (All t f@(All _ _)) = miniscope (All t (miniscope f))
miniscope (Exists t f@(All _ _)) = miniscope (Exists t (miniscope f))
miniscope (Exists t f@(Exists _ _)) = miniscope (Exists t (miniscope f))
miniscope p = Formula.map miniscope p

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

-- TODO(mert): All fresh variables are named $k^(n)$. This is not ideal, find a
-- better solution.
freshVariable :: Int -> Term
freshVariable i = Variable (newName i)
    where newName 0 = "k"
          newName n = newName (n - 1) ++ "'"

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
type ExistsP = (Int, Term)
deconsSeqExists :: Formula -> ([ExistsP], Formula)
deconsSeqExists (Exists ta (Exists tb p)) =
    ([(inNumConj p ta, ta), (inNumConj p tb, tb)] ++ fst (deconsSeqExists p), p)
deconsSeqExists (Exists ta p) = ([(inNumConj p ta, ta)], p)
deconsSeqExists f = ([], f)

-- | Reconstructs a `Formula` from the output of `deconsSeqExists`.
reconsSeqExists :: [ExistsP] -> Formula -> Formula
reconsSeqExists ((_, t):ds) p = Exists t (reconsSeqExists ds p)
reconsSeqExists [] p = p

-- | Deconstructs a sequence of `All`s.
type AllP = (Int, Term)
deconsSeqAll :: Formula -> ([AllP], Formula)
deconsSeqAll (All ta (All tb p)) =
    ([(inNumConj p ta, ta), (inNumConj p tb, tb)] ++ fst (deconsSeqAll p), p)
deconsSeqAll (All ta p) = ([(inNumConj p ta, ta)], p)
deconsSeqAll f = ([], f)

-- | Reconstructs a `Formula` from the output of `deconsSeqAll`.
reconsSeqAll :: [AllP] -> Formula -> Formula
reconsSeqAll ((_, t):ds) p = All t (reconsSeqAll ds p)
reconsSeqAll [] p = p

-- | Sort the quantifiers of a `Formula`. (Prenex sorting)
quantifierSort :: Formula -> Formula
quantifierSort f@(Exists _ (Exists _ p)) =
    reconsSeqExists st (quantifierSort p)
    where st = reverse (L.sortOn fst (fst (deconsSeqExists f)))
quantifierSort f@(All _ (All _ p)) =
    reconsSeqAll st (quantifierSort p)
    where st = reverse (L.sortOn fst (fst (deconsSeqAll f)))
quantifierSort f = Formula.map quantifierSort f

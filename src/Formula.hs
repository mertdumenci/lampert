{-|
    Defines a First-order logical formula data type (@Formula@) and relevant
    operations (NNF, DNF, CNF, etc.)
-}

module Formula (
    Term (..),
    Formula (..),
    isAnd,
    isOr,
    Formula.map,
    vars,
    bound,
    free,
    binds,
    nnf,
    cnf,
    dnf,
    rename
) where

import Data.Char
import qualified Data.List as L
import qualified Data.Set as S

-- | A First-order logical term.
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

-- | A First-order logical formula.
data Formula =
    T
    | F
    | Pred String [Term]
    | Not Formula

    | And Formula Formula
    | Or Formula Formula
    | Impl Formula Formula
    | Iff Formula Formula

    | Exists Term Formula
    | Forall Term Formula
    deriving (Eq, Ord)

-- | Whether or not the given formula is a conjunction.
isAnd :: Formula -> Bool
isAnd (And _ _) = True
isAnd _ = False

-- | Whether or not the given formula is a disjunction.
isOr :: Formula -> Bool
isOr (Or _ _) = True
isOr _ = False

-- | Applies a formula transformation on the subformulas of a formula.
map :: (Formula -> Formula) -> Formula -> Formula
map f (Not p) = Not (f p)
map f (And p q) = And (f p) (f q)
map f (Or p q) = Or (f p) (f q)
map f (Impl p q) = Impl (f p) (f q)
map f (Iff p q) = Iff (f p) (f q)
map f (Exists t p) = Exists t (f p)
map f (Forall t p) = Forall t (f p)
map _ p = p

instance Show Formula where
    show T = "⊤"
    show F = "⊥"
    show (Pred n ts) =
        L.map toUpper n ++ L.intercalate "" (L.map show ts)
    show (Not p) =
        "!" ++ "(" ++ show p ++ ")"
    show (And p q) =
        "(" ++ show p ++ " ∧ " ++ show q ++ ")"
    show (Or p q) =
        "(" ++ show p ++ " ∨ " ++ show q ++ ")"
    show (Impl p q) =
        show p ++ " -> " ++ show q
    show (Iff p q) =
        show p ++ " <-> " ++ show q
    show (Exists t p) =
        "E" ++ show t ++ ". (" ++ show p ++ ")"
    show (Forall t p) =
        "A" ++ show t ++ ". (" ++ show p ++ ")"

-- | Finds all variables in a formula. (Free and bound.)
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
        vars' (Forall _ f') s = vars' f' s
        vars' _ s = s

-- | Finds all bound variables in a formula.
bound :: Formula -> S.Set Term
bound f =
    bound' f S.empty
    where
        bound' (Not f') s = bound' f' s
        bound' (And fa fb) s = S.union (bound' fa s) (bound' fb s)
        bound' (Or fa fb) s = S.union (bound' fa s) (bound' fb s)
        bound' (Impl fa fb) s = S.union (bound' fa s) (bound' fb s)
        bound' (Iff fa fb) s = S.union (bound' fa s) (bound' fb s)
        bound' (Exists t f') s = S.insert t (bound' f' s)
        bound' (Forall t f') s = S.insert t (bound' f' s)
        bound' _ s = s

-- | Finds all free variables in a formula.
free :: Formula -> S.Set Term
free f = S.difference (vars f) (bound f)

-- | Whether or not a given variable @t@ binds a given formula @p@.
-- (i.e. @t@ ∈ Free(p))
binds :: Formula -> Term -> Bool
binds p t = S.member t (free p)

-- | Finds the total number of quantifiers in a formula. (Recursively.)
numQuantifiers :: Formula -> Int
numQuantifiers T = 0
numQuantifiers F = 0
numQuantifiers (Pred _ _) = 0
numQuantifiers (Not p) = numQuantifiers p
numQuantifiers (And p q) = numQuantifiers p + numQuantifiers q
numQuantifiers (Or p q) = numQuantifiers p + numQuantifiers q
numQuantifiers (Impl p q) = numQuantifiers p + numQuantifiers q
numQuantifiers (Iff p q) = numQuantifiers p + numQuantifiers q
numQuantifiers (Forall _ p) = numQuantifiers p + 1
numQuantifiers (Exists _ p) = numQuantifiers p + 1

-- | Converts a formula into Negation Normal Form (NNF.)
nnf :: Formula -> Formula
nnf (Not T) = F
nnf (Not F) = T
nnf (Not (Not p)) = nnf p
nnf (Not (And p q)) = Formula.map nnf $ Or (Not p) (Not q)
nnf (Not (Or p q)) = Formula.map nnf $ And (Not p) (Not q)
nnf (Not (Impl p q)) = Formula.map nnf $ And p (Not q)
nnf (Not (Iff p q)) = Formula.map nnf $ Or (And p (Not q)) (And (Not p) q)
nnf (Not (Forall t p)) = Formula.map nnf $ Exists t (Not p)
nnf (Not (Exists t p)) = Formula.map nnf $ Forall t (Not p)
nnf p = Formula.map nnf p

-- | Converts a formula into Conjunctive Normal Form (CNF.)
cnf :: Formula -> Formula
cnf (Or (And p q) z) = And (cnf $ Or p z) (cnf $ Or q z)
cnf (Or p (And q z)) = And (cnf $ Or p q) (cnf $ Or p z)
cnf p = Formula.map cnf p

-- | Converts a formula into Disjunctive Normal Form (DNF.)
dnf :: Formula -> Formula
dnf (And (Or p q) z) = Or (dnf $ And p z) (dnf $ And q z)
dnf (And p (Or q z)) = Or (dnf $ And p q) (dnf $ And p z)
dnf p = Formula.map dnf p

-- | Generates a new variable @k{n}@ where @n@ is given.
-- TODO(mert): @k{n}@ might exist in the original formula. Find a better way.
freshVariable :: Int -> Term
freshVariable n = Variable ("k" ++ show n)

-- | Applies a term transformation on every term in a formula.
mapTerm :: (Term -> Term) -> Formula -> Formula
mapTerm m (Pred s ts) = Pred s (m <$> ts)
mapTerm m (Exists t p) = Exists (m t) (mapTerm m p)
mapTerm m (Forall t p) = Forall (m t) (mapTerm m p)
mapTerm m p = Formula.map (mapTerm m) p

-- | Replaces all instances of term @s@ with a term @d@ in a formula.
replaceTerm :: Term -> Term -> Formula -> Formula
replaceTerm s d = mapTerm (\t -> if t == s then d else t)

-- | Renames variables in a formula s.t. no two different quantifiers bind
-- the same variable, using the algorithm described in
-- Nonnengart & Weidenbach '01.
rename :: Formula -> Formula
rename f = rename' f 1

rename' :: Formula -> Int -> Formula
rename' f@(Pred _ _) _ = f
rename' (Not p) i = Not (rename' p i)
rename' (And p q) i = And (rename' p i) (rename' q (i + numQuantifiers p))
rename' (Or p q) i = Or (rename' p i) (rename' q (i + numQuantifiers p))
rename' (Impl p q) i = Impl (rename' p i) (rename' q (i + numQuantifiers p))
rename' (Iff p q) i = Iff (rename' p i) (rename' q (i + numQuantifiers p))
rename' (Exists t f') i = Exists fv $ rename' (replaceTerm t fv f') (i + 1)
    where fv = freshVariable i
rename' (Forall t f') i = Forall fv $ rename' (replaceTerm t fv f') (i + 1)
    where fv = freshVariable i

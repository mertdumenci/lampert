
{-# LANGUAGE LambdaCase #-}

module Formula (
    Term (..),
    Formula (..),
    nnf,
    miniscope,
    partialPrenex
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
        L.map toLower n ++ "(" ++ (L.intercalate ", " $ L.map show ts) ++ ")"
    
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
            L.map toUpper n ++ (L.intercalate "" $ L.map show ts)
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
    if p' /= p then partialPrenex $ p' else p'
    where
        p' = Formula.map partialPrenex p

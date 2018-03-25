
module Formula (
    Term (..),
    Formula (..),
    nnf,
    free,
    bound,
    vars
) where

import Data.List
import Data.Char
import qualified Data.Set as S

data Term =
    Constant String
    | Variable String
    | Function String [Term]
    deriving (Eq, Ord)

instance Show Term where
    show (Constant n) = map toUpper n
    show (Variable n) = map toLower n
    show (Function n ts) =
        map toLower n ++ "(" ++ (intercalate ", " $ map show ts) ++ ")"
    
data Formula =
    -- Literals
    T
    | F
    | Predicate String [Term]
    | Negation Formula
    -- Binary connectives
    | Conjunction Formula Formula
    | Disjunction Formula Formula
    | Implication Formula Formula
    | Iff Formula Formula
    -- Quantifiers
    | Exists [Term] Formula
    | All [Term] Formula
    deriving (Eq, Ord)

instance Show Formula where
    show f = case f of
        T -> "⊤"
        F -> "⊥"
        Predicate n ts ->
            map toLower n ++ "(" ++ (intercalate ", " $ map show ts) ++ ")"
        Negation f' ->
            "¬" ++ "(" ++ show f' ++ ")"
        Conjunction fa fb ->
            show fa ++ " ∧ " ++ show fb
        Disjunction fa fb ->
            show fa ++ " ∨ " ++ show fb
        Implication fa fb ->
            show fa ++ " → " ++ show fb
        Iff fa fb ->
            show fa ++ " ⇔ " ++ show fb
        Exists ts f' ->
            "E" ++ (intercalate ", " $ map show ts) ++ ". (" ++ show f' ++ ")"
        All ts f' ->
            "A" ++ (intercalate ", " $ map show ts) ++ ". (" ++ show f' ++ ")"

vars :: Formula -> S.Set Term
vars f =
    vars' f S.empty
    where
        folder s v@(Variable _) = S.insert v s
        folder s _ = s

        vars' (Predicate _ ts) s = foldl folder s ts
        vars' (Negation f') s = vars' f' s
        vars' (Conjunction fa fb) s = S.union (vars' fa s) (vars' fb s)
        vars' (Disjunction fa fb) s = S.union (vars' fa s) (vars' fb s)
        vars' (Implication fa fb) s = S.union (vars' fa s) (vars' fb s)
        vars' (Iff fa fb) s = S.union (vars' fa s) (vars' fb s)
        vars' (Exists _ f') s = vars' f' s
        vars' (All _ f') s = vars' f' s
        vars' _ s = s

bound :: Formula -> S.Set Term
bound f = 
    bound' f S.empty
    where
        folder s v@(Variable _) = S.insert v s
        folder s _ = s

        bound' (Exists ts f') s = S.union (foldl folder s ts) (bound' f' s)
        bound' (All ts f') s = S.union (foldl folder s ts) (bound' f' s)
        bound' (Negation f') s = bound' f' s
        bound' (Conjunction fa fb) s = S.union (bound' fa s) (bound' fb s)
        bound' (Disjunction fa fb) s = S.union (bound' fa s) (bound' fb s)
        bound' (Implication fa fb) s = S.union (bound' fa s) (bound' fb s)
        bound' (Iff fa fb) s = S.union (bound' fa s) (bound' fb s)
        bound' _ s = s

free :: Formula -> S.Set Term
free f =
    S.difference (vars f) (bound f)

nnf :: Formula -> Formula
nnf f = case f of
    Negation T -> F
    Negation F -> T
    Negation (Negation f') -> nnf f'
    Negation (Conjunction fa fb) ->
        Disjunction (nnf $ Negation fa) (nnf $ Negation fb)
    Negation (Disjunction fa fb) ->
        Conjunction (nnf $ Negation fa) (nnf $ Negation fb)
    Negation (All ts f') ->
        Exists ts (nnf $ Negation f')
    Negation (Exists ts f') ->
        All ts (nnf $ Negation f')
    Implication fa fb ->
        Disjunction (nnf $ Negation fa) (nnf fb)
    Iff fa fb ->
        Conjunction
            (Implication (nnf fa) (nnf fb))
            (Implication (nnf fb) (nnf fa))
    
    Negation f' ->
        Negation (nnf f')
    Conjunction fa fb ->
        Conjunction (nnf fa) (nnf fb)
    Disjunction fa fb ->
        Disjunction (nnf fa) (nnf fb)
    Exists ts f' ->
        Exists ts (nnf f')
    All ts f' ->
        All ts (nnf f')

    _ -> f
    
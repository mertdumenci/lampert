{-|
    Implements the 'purification' algorithm described in Lampert (2017) p. 8.

    Takes any FOL `Formula`, and returns a FOLDNF that preserves the truth
    conditions.
-}

module Purification (
    purify
) where

import Formula
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import qualified Data.Set as S

-- | Inverse prenexing. Pushes quantifiers inwards as much as possible
-- by recursive application of the inverse PN laws.
-- (Note that this doesn't mean that the quantifiers are pushed as much
-- as possible in general.)
miniscope :: Formula -> Formula
miniscope (Forall t p) = pushForall t (miniscope p)
miniscope (Exists t p) = pushExists t (miniscope p)
miniscope p = Formula.map miniscope p

-- | Pushes an existential quantifier as much as possible inside a
-- formula (by recursive application of the inverse PN laws.)
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

-- | Pushes a universal quantifier as much as possible inside a
-- formula (by recursive application of the inverse PN laws.)
pushForall :: Term -> Formula -> Formula
pushForall t f =
    if push == f then Forall t f else push
    where
    push = case f of
        (Or a b) | a `binds` t && b `binds` t ->
            f
        (Or a b) | a `binds` t ->
            Or (pushForall t a) b
        (Or a b) | b `binds` t ->
            Or a (pushForall t b)
        (And a b) | a `binds` t && b `binds` t ->
            And (pushForall t a) (pushForall t b)
        (And a b) | a `binds` t ->
            And (pushForall t a) b
        (And a b) | b `binds` t ->
            And a (pushForall t b)
        _ -> f

-- | Groups together universal quantifiers separated by disjunctions
-- and existential quantifiers separated by conjunctions.
partialPrenex :: Formula -> Formula
partialPrenex (Or (Forall t p) q) = Forall t (partialPrenex (Or p q))
partialPrenex (Or p (Forall t q)) = Forall t (partialPrenex (Or p q))
partialPrenex (And (Exists t p) q) = Exists t (partialPrenex (And p q))
partialPrenex (And p (Exists t q)) = Exists t (partialPrenex (And p q))
partialPrenex p =
    if p' /= p then partialPrenex p' else p'
    where
        p' = Formula.map partialPrenex p

type ExistsP = (Term, Int)
-- | Deconstructs a sequence of existential quantifiers into a list of
-- (quantifier, (number of conjuncts the quantified variable binds)) pairs
-- and the inner formula that the sequence of quantifiers bind.
--
-- e.g. @deconsExists@ (ExEyEz. Fx ∧ Qxy ∧ Fz) =
--          ([(x, 2), (y, 1), (z, 1)], Fx ∧ Qxy ∧ Fz)
deconsExists :: Formula -> ([ExistsP], Formula)
deconsExists (Exists ta (Exists tb p)) =
    let (more, innerFormula) = deconsExists p in
    ([(ta, bindsNumConj p ta), (tb, bindsNumConj p tb)] ++ more, innerFormula)
deconsExists (Exists ta p) = ([(ta, bindsNumConj p ta)], p)
deconsExists f = ([], f)

-- | Reconstructs a formula from the output of @deconsExists@.
reconsExists :: [ExistsP] -> Formula -> Formula
reconsExists ((t, _):ds) p = Exists t (reconsExists ds p)
reconsExists [] p = p

-- | Finds the number of disjuncts a variable binds in a disjunction.
bindsNumDisj :: Formula -> Term -> Int
bindsNumDisj (Or p q) t = bindsNumDisj p t + bindsNumDisj q t
bindsNumDisj p t = if p `binds` t then 1 else 0

-- | Finds the number of conjuncts a variable binds in a conjunction.
bindsNumConj :: Formula -> Term -> Int
bindsNumConj (And p q) t = bindsNumConj p t + bindsNumConj q t
bindsNumConj p t = if p `binds` t then 1 else 0

type ForallP = (Term, Int)
-- | Deconstructs a sequence of universal quantifiers into a list of
-- (quantifier, (number of disjuncts the quantified variable binds)) pairs
-- and the inner formula that the sequence of quantifiers bind.
--
-- e.g. @deconsForall@ (AxAyAz. Fx ∨ Qxy ∨ Fz) =
--          ([(x, 2), (y, 1), (z, 1)], Fx ∨ Qxy ∨ Fz)
deconsForall :: Formula -> ([ForallP], Formula)
deconsForall (Forall ta (Forall tb p)) =
    let (more, innerFormula) = deconsForall p in
        ([(ta, bindsNumDisj p ta), (tb, bindsNumDisj p tb)] ++ more, innerFormula)
deconsForall (Forall ta p) = ([(ta, bindsNumDisj p ta)], p)
deconsForall f = ([], f)

-- | Reconstructs a formula from the output of @deconsForall@.
reconsForall :: [ForallP] -> Formula -> Formula
reconsForall ((t, _):ds) p = Forall t (reconsForall ds p)
reconsForall [] p = p

type OrP = (Formula, S.Set Term)
-- | Deconstructs a disjunction into a list of (disjunct, vars in disjunct)
-- pairs.
deconsOr :: Formula -> [OrP]
deconsOr (And p q) = deconsOr p ++ deconsOr q
deconsOr p = [(p, vars p)]

-- | Reconstructs a disjunction from the output of @deconsOr@.
reconsOr :: [OrP] -> Formula
reconsOr ((p, _):is)
    | L.null is = p
    | otherwise = Or p (reconsOr is)

type AndP = (Formula, S.Set Term)
-- | Deconstructs a conjunction a list of (conjunct, vars in conjunct)
-- pairs.
deconsAnd :: Formula -> [AndP]
deconsAnd (And p q) = deconsAnd p ++ deconsAnd q
deconsAnd p = [(p, vars p)]

-- | Reconstructs a conjunction from the output of @deconsAnd@.
reconsAnd :: [AndP] -> Formula
reconsAnd ((p, _):is)
    | L.null is = p
    | otherwise = And p (reconsAnd is)

-- | Combines the quantifier and scope sorting steps in Lampert (2017) p. 8.
-- and renames the quantified variables such that no two quantifiers bind
-- the same variable as a result of the sorting process.
--
-- The sorts are applied on sequences of universal (existential) quantifiers.
-- The two sorts are:
--      The quantifiers in the sequence, in descending order of disjuncts
--      (conjuncts) the quantified variable binds. (Quantifier sorting)
--      
--      The disjuncts (conjuncts) in the inner formula of the sequence,
--      such that if a variable @x@ appears after @y@ in the sorted quantifier
--      sequence, all disjuncts (conjuncts) that contain @x@ come after @y@.
--      (Scope sorting)
--
-- e.g. @sort@ (ExEyEz. Fz ∧ (ApAqAw. Qwz ∨ Fp ∨ Qwq) ∧ Qzy ∧ Qxy) =
--           (EzEyEx. Fz ∧ (AwApAq. Qwz ∨ Fp ∨ Qwq) ∧ Qzy ∧ Qxy)
sort :: Formula -> Formula
sort = sort' . rename . partialPrenex

-- TODO(mert): Add comments to this process.
sort' :: Formula -> Formula
sort' f@(Exists _ (Exists _ _)) =
    reconsExists sortedQuantifierVars (sort sortedP)
    where
        (quantifierVars, p) = deconsExists f
        scopeMap = M.fromList quantifierVars
        scope v = fromMaybe 0 (M.lookup v scopeMap)
        key (_, conjunctVars) = minimum (S.map scope conjunctVars)

        sortedConjuncts = reverse (L.sortOn key (deconsAnd p))
        sortedP = if isAnd p then reconsAnd sortedConjuncts else p

        sortedQuantifierVars = reverse (L.sortOn snd quantifierVars)
sort' f@(Forall _ (Forall _ _)) =
    reconsForall sortedQuantifierVars (sort sortedP)
    where
        (quantifierVars, p) = deconsForall f
        scopeMap = M.fromList quantifierVars
        scope v = fromMaybe 0 (M.lookup v scopeMap)
        key (_, disjunctVars) = minimum (S.map scope disjunctVars)

        sortedDisjuncts = reverse (L.sortOn key (deconsOr p))
        sortedP = if isOr p then reconsOr sortedDisjuncts else p

        sortedQuantifierVars = reverse (L.sortOn snd quantifierVars)
sort' f = Formula.map sort' f

-- | Implements the scope conversion process detailed in Lampert (2017) p. 7.
--
-- If a disjunction is universally quantified such that the quantified variable
-- binds both disjuncts (Ax. Fx ∨ Qx), convert the inner formula to a CNF.
--
-- If a conjunction is existentially quantified such that the quantified
-- variable binds both conjuncts (Ax. Fx ∧ Qx), convert the inner formula to a
-- DNF.
convertScope :: Formula -> Formula
convertScope f = case f of
    (Forall t (Or p q)) | p `binds` t && q `binds` t -> Formula.map cnf f
    (Exists t (And p q)) | p `binds` t && q `binds` t -> Formula.map dnf f
    _ -> if f' /= f then convertScope f' else f'
    where
        f' = Formula.map convertScope f

-- | Apply a function on a value repeatedly until you find a fixpoint.
stable :: (Eq a) => (a -> a) -> a -> a
stable f x = if x' == x then x' else stable f x'
    where x' = f x

-- | The full purification process detailed in Lampert (2017) p. 8. Takes any
-- @Formula@, and returns a FOLDNF.
purify :: Formula -> Formula
purify f = rename . dnf $ f'
    where f' = stable (convertScope . miniscope . sort . miniscope . nnf) f

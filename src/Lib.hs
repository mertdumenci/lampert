module Lib (
    someFunc
) where

import qualified Formula as F

randomFormula :: F.Formula
randomFormula =
    F.All x (
        F.Implication (
            F.Exists y (
                F.Conjunction (
                    F.Predicate "p" [x, y]
                ) (
                    F.Predicate "p" [x, z]
                )
            )
        ) (
            F.Exists w (
                F.Predicate "p" [x, w]
            )
        )
    )
    where x = F.Variable "x"
          y = F.Variable "y"
          z = F.Variable "z"
          w = F.Variable "w"

someFunc :: IO ()
someFunc = do
    putStrLn $ show randomFormula
    putStrLn $ show $ F.nnf randomFormula
    putStrLn $ show $ F.miniscope . F.nnf $ randomFormula

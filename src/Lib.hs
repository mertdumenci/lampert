module Lib (
    someFunc
) where

import qualified Formula as F

randomFormula :: F.Formula
randomFormula =
    F.All x (
        F.Impl (
            F.Exists y (
                F.And (
                    F.Pred "p" [x, y]
                ) (
                    F.Pred "p" [x, z]
                )
            )
        ) (
            F.Exists w (
                F.Pred "p" [x, w]
            )
        )
    )
    where x = F.Variable "x"
          y = F.Variable "y"
          z = F.Variable "z"
          w = F.Variable "w"

formula2 :: F.Formula
formula2 =
    F.Exists y (
        F.All x (
            F.Not (
                F.Impl (
                    F.Or (
                            F.And (
                                F.Not $ F.Pred "F" [x, x]
                            ) (
                                F.Pred "G" [y]
                            )
                        ) (
                            F.Pred "H" [x, y]
                        )
                    ) (
                        F.Not $ F.Pred "P" []
                    )
            )
        )
    )
    where x = F.Variable "x"
          y = F.Variable "y"



formula3 :: F.Formula
formula3 =
    F.All x (
        F.And (F.Pred "P" [x]) (F.Pred "Q" [])
    )
    where x = F.Variable "x"


formula4 :: F.Formula
formula4 =
    F.All x ( 
        F.Exists x (
            F.And (F.Pred "P" [x]) (F.Pred "Q" [])
        )
    )
    where x = F.Variable "x"

someFunc :: IO ()
someFunc = do
    putStrLn $ "Original formula " ++ show formula2
    let n2 = F.nnf formula2
    putStrLn $ "NNF formula " ++ show n2
    let m2 = F.miniscope n2
    putStrLn $ "Miniscoped formula " ++ show m2
    putStrLn . show $ F.miniscope formula4

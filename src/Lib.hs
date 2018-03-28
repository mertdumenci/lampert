
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

formula5 :: F.Formula
formula5 =
    F.Or (
        F.Pred "P" [x]
    ) (
        F.All x (
            F.Or (
                F.Pred "P" [x]
            ) (
                F.All y (
                    F.Pred "Q" [y]
                )
            )
        )
    )
    where x = F.Variable "x"
          y = F.Variable "y"

formula6 :: F.Formula
formula6 =
    F.All x (F.Exists x (F.Pred "P" [x, y]))
    where x = F.Variable "x"
          y = F.Variable "y"

formula7 :: F.Formula
formula7 =
    F.Exists y
        (F.Exists x
            (F.And
                (F.Or (F.Pred "Q" [y]) (F.Pred "P" [x]))
                (F.Pred "P" [x])
            )
        )
    where   x = F.Variable "x"
            y = F.Variable "y"

formula8 :: F.Formula
formula8 =
    F.Exists y2
        (F.Exists y1
            (F.And
                (F.Exists y3
                    (F.And
                        (F.Pred "H" [y3])
                        (F.Pred "K" [y3])
                    )
                )
                (F.And
                    (F.Pred "F" [y1, y2])
                    (F.Pred "G" [y1])
                )
            )
        )
    where y1 = F.Variable "y1"
          y2 = F.Variable "y2"
          y3 = F.Variable "y3"


someFunc :: IO ()
someFunc = do
    -- let n2 = F.nnf formula2
    -- putStrLn $ "NNF formula " ++ show n2
    -- let m2 = F.miniscope n2
    -- putStrLn $ "Miniscoped formula " ++ show m2
    -- let r2 = F.rename formula6
    -- putStrLn $ "Renamed formula " ++ show r2
    -- putStrLn $ "Original formula: " ++ show formula7
    -- putStrLn $ "Sorted formula: " ++ show (F.sort formula7)

    let nnf = F.nnf formula8
    -- let miniscope1 = F.miniscope nnf
    let sorted = F.sort nnf
    let miniscope2 = F.miniscope sorted

    print nnf
    print sorted
    print miniscope2
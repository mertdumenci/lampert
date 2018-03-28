
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
    -- let nnf = F.nnf formula2
    -- putStrLn $ "NNF: " ++ show nnf
    -- let m1 = F.miniscope nnf
    -- putStrLn $ "First miniscope: " ++ show m1
    -- let sorted = F.sort m1
    -- putStrLn $ "Sorted: " ++ show sorted
    -- let m2 = F.miniscope sorted
    -- putStrLn $ "Second miniscope: " ++ show m2
    -- let sc = F.convertScope m2
    -- putStrLn $ "Scope conversion: " ++ show sc
    -- print " ---- "
    -- let m3 = F.miniscope sc
    -- putStrLn $ "Third miniscope: " ++ show m3
    -- let sorted2 = F.sort m3
    -- putStrLn $ "Second sorted: " ++ show m3
    -- let m4 = F.miniscope sorted2
    -- putStrLn $ "Fourth miniscope: " ++ show m4
    -- let sc2 = F.convertScope m4
    -- putStrLn $ "Second scope conversion: " ++ show sc2
    -- let m5 = F.miniscope sc2
    print formula2
    print (F.purify formula2)

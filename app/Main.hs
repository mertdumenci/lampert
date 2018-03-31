module Main where

import Lib

formula1 :: Lib.Formula
formula1 =
    Lib.Forall x (
        Lib.Impl (
            Lib.Exists y (
                Lib.And (
                    Lib.Pred "p" [x, y]
                ) (
                    Lib.Pred "p" [x, z]
                )
            )
        ) (
            Lib.Exists w (
                Lib.Pred "p" [x, w]
            )
        )
    )
    where x = Lib.Variable "x"
          y = Lib.Variable "y"
          z = Lib.Variable "z"
          w = Lib.Variable "w"

formula2 :: Lib.Formula
formula2 =
    Lib.Exists y (
        Lib.Forall x (
            Lib.Not (
                Lib.Impl (
                    Lib.Or (
                            Lib.And (
                                Lib.Not $ Lib.Pred "F" [x, x]
                            ) (
                                Lib.Pred "G" [y]
                            )
                        ) (
                            Lib.Pred "H" [x, y]
                        )
                    ) (
                        Lib.Not $ Lib.Pred "P" []
                    )
            )
        )
    )
    where x = Lib.Variable "x"
          y = Lib.Variable "y"



formula3 :: Lib.Formula
formula3 =
    Lib.Forall x (
        Lib.And (Lib.Pred "P" [x]) (Lib.Pred "Q" [])
    )
    where x = Lib.Variable "x"


formula4 :: Lib.Formula
formula4 =
    Lib.Forall x (
        Lib.Exists x (
            Lib.And (Lib.Pred "P" [x]) (Lib.Pred "Q" [])
        )
    )
    where x = Lib.Variable "x"

formula5 :: Lib.Formula
formula5 =
    Lib.Or (
        Lib.Pred "P" [x]
    ) (
        Lib.Forall x (
            Lib.Or (
                Lib.Pred "P" [x]
            ) (
                Lib.Forall y (
                    Lib.Pred "Q" [y]
                )
            )
        )
    )
    where x = Lib.Variable "x"
          y = Lib.Variable "y"

formula6 :: Lib.Formula
formula6 =
    Lib.Forall x (Lib.Exists x (Lib.Pred "P" [x, y]))
    where x = Lib.Variable "x"
          y = Lib.Variable "y"

formula7 :: Lib.Formula
formula7 =
    Lib.Exists y
        (Lib.Exists x
            (Lib.And
                (Lib.Or (Lib.Pred "Q" [y]) (Lib.Pred "P" [x]))
                (Lib.Pred "P" [x])
            )
        )
    where   x = Lib.Variable "x"
            y = Lib.Variable "y"

formula8 :: Lib.Formula
formula8 =
    Lib.Exists y2
        (Lib.Exists y1
            (Lib.And
                (Lib.Exists y3
                    (Lib.And
                        (Lib.Pred "H" [y3])
                        (Lib.Pred "K" [y3])
                    )
                )
                (Lib.And
                    (Lib.Pred "F" [y1, y2])
                    (Lib.Pred "G" [y1])
                )
            )
        )
    where y1 = Lib.Variable "y1"
          y2 = Lib.Variable "y2"
          y3 = Lib.Variable "y3"

main :: IO ()
main = do
    putStrLn $ "Initial formula: " ++ show formula2
    putStrLn $ "FOLDNF: " ++ show (Lib.purify formula2)

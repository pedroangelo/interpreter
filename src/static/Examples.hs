module Examples where

import Syntax

factorial n = Application factorial' (Int n)
factorial' = LetRec "fact" (Abstraction "n" $ If (Equal (Variable "n") (Int 0)) (Int 1) (Multiplication (Variable "n") (Application (Variable "fact") (Subtraction (Variable "n") (Int 1))))) (Variable "fact")

power n p = Application (Application power' (Int n)) (Int p)
power' = LetRec "power" (Abstraction "n" $ Abstraction "p" $ If (Equal (Variable "p") (Int 0)) (Int 1) (Multiplication (Variable "n") (Application (Application (Variable "power") (Variable "n")) (Subtraction (Variable "p") (Int 1))))) (Variable "power")

moddiv m n = Application (Application moddiv' (Int m)) (Int n)
moddiv' = Abstraction "m" $ Abstraction "n" $ Let "quotient" (Division (Variable "m") (Variable "n")) (Subtraction (Variable "m") (Multiplication (Variable "n") (Variable "quotient")))

module Examples where

import Syntax

lambda_I = Abstraction "i" $ Variable "i"

factorial n = Application factorial' n
factorial' = LetRec "fact" (Abstraction "n" $ If (Equal (Variable "n") (Int 0)) (Int 1) (Multiplication (Variable "n") (Application (Variable "fact") (Subtraction (Variable "n") (Int 1))))) (Variable "fact")

power n p = Application (Application power' n) p
power' = LetRec "power" (Abstraction "n" $ Abstraction "p" $ If (Equal (Variable "p") (Int 0)) (Int 1) (Multiplication (Variable "n") (Application (Application (Variable "power") (Variable "n")) (Subtraction (Variable "p") (Int 1))))) (Variable "power")

moddiv m n = Application (Application moddiv' m) n
moddiv' = Abstraction "m" $ Abstraction "n" $ Let "quotient" (Division (Variable "m") (Variable "n")) (Subtraction (Variable "m") (Multiplication (Variable "n") (Variable "quotient")))

not' = Abstraction "b" $ If (Variable "b") (Bool False) (Bool True)

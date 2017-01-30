module Examples where

-- Syntax & Types
import Syntax
import Types

lambda_I = Abstraction "i" $ Variable "i"

lambda_I_ascribed = Abstraction "i" $ Ascription (Variable "i") IntType

lambda_I_annotated = Annotation "i" IntType $ Variable "i"

lambda_I_error = Annotation "i" IntType $ Ascription (Variable "i") BoolType

factorial_func n = Application factorial (Int n)
factorial = LetRec "fact" (Abstraction "n" $ If (Equal (Variable "n") (Int 0)) (Int 1) (Multiplication (Variable "n") (Application (Variable "fact") (Subtraction (Variable "n") (Int 1))))) (Variable "fact")

power_func n p = Application (Application power (Int n)) (Int p)
power = LetRec "power" (Abstraction "n" $ Abstraction "p" $ If (Equal (Variable "p") (Int 0)) (Int 1) (Multiplication (Variable "n") (Application (Application (Variable "power") (Variable "n")) (Subtraction (Variable "p") (Int 1))))) (Variable "power")

moddiv_func m n = Application (Application moddiv (Int m)) (Int n)
moddiv = Abstraction "m" $ Abstraction "n" $ Let "quotient" (Division (Variable "m") (Variable "n")) (Subtraction (Variable "m") (Multiplication (Variable "n") (Variable "quotient")))

not_func b = Application not' (Bool b)
not' = Abstraction "b" $ If (Variable "b") (Bool False) (Bool True)

gcd_func a b = Application (Application gcd' (Int a)) (Int b)
gcd' = LetRec "gcd" (Abstraction "a" $ Abstraction "b" $ If (Equal (Variable "b") (Int 0)) (Variable "a") (Application (Application (Variable "gcd") (Variable "b")) (Application (Application moddiv (Variable "a")) (Variable "b")))) (Variable "gcd")

module Static.Examples where

-- Syntax & Types
import Static.Syntax
import Static.Types

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

-- Recursive Types

-- List of Int
intList = Mu "L" $ SumType (UnitType) (ProductType IntType (VarType "L"))
intList' = SumType UnitType (ProductType IntType (Mu "L" (SumType UnitType (ProductType IntType (VarType "L")))))

nil = Fold intList $ LeftTag Unit intList'

cons = Abstraction "n" $ Abstraction "l" $ Fold intList $ RightTag (Pair (Variable "n") (Variable "l")) intList'

isnil = Abstraction "l" $ Case (Unfold intList $ Variable "l") ("x", Bool True) ("x", Bool False)

hd = Abstraction "l" $ Case (Unfold intList $ Variable "l") ("x", (Int (-1))) ("x", First $ Variable "x")

tl = Abstraction "l" $ Case (Unfold intList $ Variable "l") ("x", nil) ("x", Second $ Variable "x")

list1 = Application (Application cons (Int 1)) nil

list2 = Application (Application cons (Int 2)) list1

sumlist = Fix $ Abstraction "s" $ Abstraction "l" $ If (Application (isnil) (Variable "l")) (Int 0) (Addition (Application (hd) (Variable "l")) (Application (Variable "s") (Application (tl) (Variable "l"))))

mapInt = Fix $ Abstraction "m" $ Abstraction "f" $ Abstraction "l" $ If (Application isnil (Variable "l")) nil (Application (Application (cons) (Application (Variable "f") (Application (hd) (Variable "l")))) (Application (Application (Variable "m") (Variable "f")) (Application (tl) (Variable "l"))))

map_func f l =  Application (Application (mapInt) f) l

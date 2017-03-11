module Examples where

-- Syntax & Types
import Syntax
import Types

-- STANDARD TERMS

-- (λx.x) : T1 -> T1
lambda_I = Abstraction "x" (Variable "x")

-- (λx.λy.x) : T1 -> T2 -> T1
lambda_K = Abstraction "x" (Abstraction "y" (Variable "x"))

-- (λx.λy.λz.xz(yz)) : (T2 -> T1 -> T) -> (T2 -> T1) -> T2 -> T
lambda_S = Abstraction "x" (Abstraction "y" (Abstraction "z" (Application (Application (Variable "x") (Variable "z")) (Application (Variable "y") (Variable "z")))))

-- (λx.λy.λz.x (y z)) : (T1 -> T) -> (T2 -> T1) -> T2 -> T
lambda_B = Abstraction "x" (Abstraction "y" (Abstraction "z" (Application (Variable "x") (Application (Variable "y") (Variable "z")))))

-- (λx.λy.λz.x z y) : (T1 -> T2 -> T) -> T2 -> T1 -> T
lambda_C = Abstraction "x" (Abstraction "y" (Abstraction "z" (Application (Application (Variable "x") (Variable "z")) (Variable "y"))))

-- (λx.λy.x y y) : (T1 -> T1 -> T) -> T1 -> T
lambda_W = Abstraction "x" (Abstraction "y" (Application (Application (Variable "x") (Variable "y")) (Variable "y")))

-- (λx.λy.y (x x y)) : undefined
lambda_U = Abstraction "x" (Abstraction "y" (Application (Variable "y") (Application (Application (Variable "x") (Variable "x")) (Variable "y"))))

-- (\x.x x) : undefined
lambda_omega = Abstraction "x" (Application (Variable  "x") (Variable "x"))

-- ((\x.x x) (\x.x x)) : undefined
lambda_Omega = Application (lambda_omega) (lambda_omega)

-- (λg.(λx.g (x x)) (λx.g (x x))) : undefined
lambda_Y = Abstraction "g" (Application (Abstraction "x" (Application (Variable "g") (Application (Variable "x") (Variable "x")))) (Abstraction "x" (Application (Variable "g") (Application (Variable "x") (Variable "x")))))

-- Tested Examples
-- Still need to test execution with casts

-- (λx . x) 1 : Int
-- Expression: (app (abs int x\x) (zero))
-- Compiled: (app (cast (abs int (W1\ W1)) (arrow int int) _T1 (arrow int int)) (cast zero int _T1 int))
tested_1 = Application (Annotation "x" IntType $ Variable "x") (Int 0)

-- (λx : ? . x) 0 : ?
-- Expression: (app (abs dyn x\x) (zero))
-- Compiled: (app (cast (abs dyn (W1\ W1)) (arrow dyn dyn) _T1 (arrow dyn dyn)) (cast zero int _T1 dyn))
tested_1_dyn = Application (Annotation "x" DynType $ Variable "x") (Int 0)

-- (λx : Int . 0 + x) True : TypeError
-- Expression: (app (abs int (x\(add (zero) x))) (tt))
tested_2 = Application (Annotation "x" IntType (Addition (Int 0) (Variable "x"))) (Bool True)

-- (λx : ? . 0 + x) True : Int
-- Expression: (app (abs dyn (x\(add (zero) x))) (tt))
-- Compiled: (app (cast (abs dyn (W1\ add (cast zero int (_T1 W1) int) (cast W1 dyn (_T1 W1) int))) (arrow dyn int) _T2 (arrow dyn int)) (cast tt bool _T2 dyn))
tested_2_dyn = Application (Annotation "x" DynType (Addition (Int 0) (Variable "x"))) (Bool True)

tested_3 = Let "id"
	(Abstraction "x" (Variable "x"))
	(If
		(Application
			(Variable "id")
			(Bool True))
		(Application
			(Variable "id")
			(Int 1))
		(Application
			(Variable "id")
			(Int 2)))

-- let id = (λx . x) in (if (id True) then (id 0) else (id 0)) : ?
-- Expression: (let (abs dyn x\x) (i\(if (app (i) (tt)) (app (i) (zero)) (app (i) (zero)))))
-- Compiled: (let (abs dyn (W1\ W1)) (W1\ if (cast (app (cast W1 (arrow dyn dyn) (_T1 W1) (arrow dyn dyn)) (cast tt bool (_T1 W1) dyn)) dyn (_T2 W1) bool) (cast (app (cast W1 (arrow dyn dyn) (_T3 W1) (arrow dyn dyn)) (cast zero int (_T3 W1) dyn)) dyn (_T2 W1) dyn) (cast (app (cast W1 (arrow dyn dyn) (_T4 W1) (arrow dyn dyn)) (cast zero int (_T4 W1) dyn)) dyn (_T2 W1) dyn)))
tested_3_dyn = Let "id"
	(Annotation "x" DynType (Variable "x"))
	(If
		(Application
			(Variable "id")
			(Bool True))
		(Application
			(Variable "id")
			(Int 1))
		(Application
			(Variable "id")
			(Int 2)))

tested_4 = Application (Abstraction "id" (If
		(Application
			(Variable "id")
			(Bool True))
		(Application
			(Variable "id")
			(Int 1))
		(Application
			(Variable "id")
			(Int 2)))) (Abstraction "x" $ Variable "x")

-- (λid : ? . if (id True) then (id 0) else (id 0)) (λx : ? . x) : ?
-- Expression: (app (abs dyn id\(if (app id tt) (app id zero) (app id zero))) (abs dyn x\x))
-- Compiled: (app (cast (abs dyn (W1\ if (cast (app (cast W1 dyn (_T1 W1) (arrow dyn dyn)) (cast tt bool (_T1 W1) dyn)) dyn (_T2 W1) bool) (cast (app (cast W1 dyn (_T3 W1) (arrow dyn dyn)) (cast zero int (_T3 W1) dyn)) dyn (_T2 W1) dyn) (cast (app (cast W1 dyn (_T4 W1) (arrow dyn dyn)) (cast zero int (_T4 W1) dyn)) dyn (_T2 W1) dyn))) (arrow dyn dyn) _T5 (arrow dyn dyn)) (cast (abs dyn (W1\ W1)) (arrow dyn dyn) _T5 dyn))
tested_4_dyn = Application (Annotation "id" DynType (If
		(Application
			(Variable "id")
			(Bool True))
		(Application
			(Variable "id")
			(Int 1))
		(Application
			(Variable "id")
			(Int 2)))) (Annotation "x" DynType $ Variable "x")

-- let incr = (λx:? . 1 + x) in incr True : Int
-- Expression: (let (abs dyn x\(add zero x)) (incr\(app incr tt)))
-- Compiled: (let (abs dyn (W1\ add (cast zero int (_T1 W1) int) (cast W1 dyn (_T1 W1) int))) (W1\ app (cast W1 (arrow dyn int) (_T2 W1) (arrow dyn int)) (cast tt bool (_T2 W1) dyn)))
tested_5_dyn = Let "incr"
	(Annotation "x" DynType $ Addition (Int 1) (Variable "x"))
	(Application (Variable "incr") (Bool True))

-- (λx : ? . if x then 1 else 2) 1 : Int
-- Expression: (app (abs dyn x\(if x zero zero)) zero)
-- Compiled: (app (cast (abs dyn (W1\ if (cast W1 dyn (_T1 W1) bool) (cast zero int (_T1 W1) int) (cast zero int (_T1 W1) int))) (arrow dyn int) _T2 (arrow dyn int)) (cast zero int _T2 dyn))
tested_6 = Application
	(Annotation "x" DynType $ If (Variable "x") (Int 1) (Int 2))
	(Int 1)

-- (λn1 . λn2 . n1 + n2) : Int -> Int -> Int
-- Expression: (abs int x\(abs int y\(add x y)))
-- Compiled: (abs int (W1\ abs int (W2\ add (cast W1 int (_T1 W1 W2) int) (cast W2 int (_T1 W1 W2) int))))
plus = Abstraction "n1" $ Abstraction "n2" $ Addition (Variable "n1") (Variable "n2")

-- (λx . if (x == 0) then True else False) : Int -> Bool
isZero = Abstraction "x" $ If (Equal (Variable "x") (Int 0)) (Bool True) (Bool False)

-- Examples to test gradual type parameters

-- (λx:? . (λy . y) x) : ? -> ?
parameters_1 = Annotation "x" DynType
	(Application
		(Abstraction "y" (Variable "y"))
		(Variable "x"))

-- (λx : ? . (λy . y) x) 1 : ?
parameters_2 = Application
	parameters_1
	(Int 1)

-- (λx : ? . (λz . z) x) (+) : ?
parameters_3 = Application
	parameters_1
	plus

-- ((λx : ? . (λz . z) x) (+)) 3 2 : ?
parameters_4 = Application
	(Application
		parameters_3
		(Int 3))
	(Int 2)

-- ((λx:? . (λy . y) x) isZero) 1 : ?
parameters_5 = Application
	(Application
		parameters_1
		isZero)
	(Int 1)

-- ((λx:? . (λy . y) x) isZero) True : ?
parameters_5_err = Application
	(Application
		parameters_1
		isZero)
	(Bool True)

-- (λx:? . if x then 1 else 2) (λx:? . (λy . y) x) True : Int
parameters_6 = Application
	(Annotation "x" DynType $ If (Variable "x") (Int 1) (Int 2))
	(Application
		(parameters_1)
		(Bool True))

-- (λx:? . if x then 1 else 2) (λx:? . (λy . y) x) 1 : Int
parameters_6_err_1 = Application
	(Annotation "x" DynType $ If (Variable "x") (Int 1) (Int 2))
	parameters_2

-- (λx:? . if x then 1 else True) (λx:? . (λy . y) x) 1 : TypeError
parameters_6_err_2 = Application
	(Annotation "x" DynType $ If (Variable "x") (Int 1) (Bool True))
	parameters_2

-- Examples of useful functions

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

-- Examples to test let and letrec

letrec_1 = LetRec "ten"
	(Abstraction "x" $
		If (Equal (Variable "x") (Int 10))
			(Int 0)
			(Addition
				(Int 1)
				(Application
					(Variable "ten")
					(Addition
						(Int 1)
						(Variable "x")))))
	(Variable "ten")

let_1 = Let "let"
	(Application
		lambda_I
		(Annotation "x" IntType $ Variable "x"))
	(Application
		(Variable "let")
		(Ascription (Bool True) DynType))

-- Examples to test Unit, Product and Sum types

pairs1 = First $ Application
	(Abstraction "x" $ If (First $ Variable "x") (Variable "x") (Variable "x"))
	(Pair (Bool True) (Int 1))

pairs1_dyn = First $ Application
	(Annotation "x" DynType $ If (First $ Variable "x") (Variable "x") (Variable "x"))
	(Pair (Bool True) (Int 1))

sums1 = Case (LeftTag (Bool True) (SumType BoolType IntType))
	("l", Application (Annotation "z" IntType $ Bool True) (Variable "l"))
	("r", Application (Annotation "z" IntType $ Bool True) (Variable "r"))

sums1_dyn = Application
	(Annotation "a" DynType $
		Case (Variable "a")
			("l", Application (Annotation "z" IntType $ Bool True) (Variable "l"))
			("r", Application (Annotation "z" IntType $ Bool True) (Variable "r")))
	(LeftTag (Bool True) (SumType BoolType IntType))

sums1_dyn_lr = Case (RightTag (Int 1) (SumType DynType DynType))
	("l", Application (Annotation "z" IntType $ Bool True) (Variable "l"))
	("r", Application (Annotation "z" IntType $ Bool True) (Variable "r"))

sums1_dyn_r = Case (RightTag (Int 1) (SumType BoolType DynType))
	("l", Application (Annotation "z" IntType $ Bool True) (Variable "l"))
	("r", Application (Annotation "z" IntType $ Bool True) (Variable "r"))

-- (app (abs dyn x\(case (x) (y\app (abs int z\(tt)) (y)) (y\app (abs int z\(tt)) (y)))) (inl int tt))

sums2 = Case (LeftTag (Bool True) (SumType BoolType IntType))
			("l", Application not' (Variable "l"))
			("r", Application isZero (Variable "r"))

sums2_1_dyn = Application
	(Annotation "a" DynType $
		Case (Variable "a")
			("l", Application not' (Variable "l"))
			("r", Application isZero (Variable "r")))
	(LeftTag (Bool True) (SumType BoolType IntType))

sums2_dyn = Case (LeftTag (Bool True) (SumType DynType DynType))
	("l", Application not' (Variable "l"))
	("r", Application isZero (Variable "r"))

sums2_dyn_r = Case (RightTag (Int 0) (SumType DynType IntType))
	("l", Application not' (Variable "l"))
	("r", Application isZero (Variable "r"))

sums2_dyn_l = Case (LeftTag (Bool True) (SumType BoolType DynType))
	("l", Application not' (Variable "l"))
	("r", Application isZero (Variable "r"))

-- Variants

variants1 = CaseVariant (Tag "b" (Bool True) (VariantType [("b", BoolType), ("i", IntType)]))
	[("b", "l", Application (Annotation "z" IntType $ Bool True) (Variable "l")),
	("i", "r", Application (Annotation "z" IntType $ Bool False) (Variable "r"))]

variants1_dyn = Application
	(Annotation "a" DynType $
		CaseVariant (Variable "a")
		[("b", "l", Application (Annotation "z" IntType $ Bool True) (Variable "l")),
		("i", "r", Application (Annotation "z" IntType $ Bool True) (Variable "r"))])
	(Tag "b" (Bool True) (VariantType [("b", BoolType), ("i", IntType)]))

variants1_dyn_lr = CaseVariant (Tag "i" (Int 1) (VariantType [("b", DynType), ("i", DynType)]))
	[("b", "l", Application (Annotation "z" IntType $ Bool True) (Variable "l")),
	("i", "r", Application (Annotation "z" IntType $ Bool True) (Variable "r"))]

variants1_dyn_r = CaseVariant (Tag "i" (Int 1) (VariantType [("b", BoolType), ("i", DynType)]))
	[("b", "l", Application (Annotation "z" IntType $ Bool True) (Variable "l")),
	("i", "r", Application (Annotation "z" IntType $ Bool True) (Variable "r"))]

variants2 = CaseVariant (Tag "b" (Bool True) (VariantType [("b", BoolType), ("i", IntType)]))
			[("b", "l", Application not' (Variable "l")),
			("i", "r", Application isZero (Variable "r"))]

variants2_1_dyn = Application
	(Annotation "a" DynType $
		CaseVariant (Variable "a")
			[("b", "l", Application not' (Variable "l")),
			("i", "r", Application isZero (Variable "r"))])
	(Tag "b" (Bool True) (VariantType [("b", BoolType), ("i", IntType)]))

variants2_dyn = CaseVariant (Tag "b" (Bool True) (VariantType [("b", DynType), ("i", DynType)]))
	[("b", "l", Application not' (Variable "l")),
	("i", "r", Application isZero (Variable "r"))]

variants2_dyn_r = CaseVariant (Tag "i" (Int 0) (VariantType [("b", DynType), ("i", IntType)]))
	[("b", "l", Application not' (Variable "l")),
	("i", "r", Application isZero (Variable "r"))]

variants2_dyn_l = CaseVariant (Tag "b" (Bool True) (VariantType [("b", BoolType), ("i", DynType)]))
	[("b", "l", Application not' (Variable "l")),
	("i", "r", Application isZero (Variable "r"))]

module Examples where

-- Syntax & Types
import Syntax
import Types

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

-- (λx:? . (λy . y) x) : ? -> A
example1 = Annotation "x" DynType
	(Application
		(Abstraction "y" (Variable "y"))
		(Variable "x"))

-- (λx : T -> T1 -> T2 . λy . λz . (xz) (yz)) : (A -> B -> C) -> (A -> B) -> A -> C
example2 = Annotation "x" (ArrowType (ParType "A") (ArrowType (ParType "B") (ParType "C")))
	(Abstraction "y"
		(Abstraction "z"
			(Application
				(Application
					(Variable "x")
					(Variable "z"))
				(Application
					(Variable "y")
					(Variable "z")))))

-- (λx : A -> B . λy . x y) : (A -> B) -> A -> B
example3 = Annotation "x" (ArrowType (ParType "A") (ParType "B"))
	(Abstraction "y"
		(Application
			(Variable "x")
			(Variable "y")))

-- (λx . if x then (λy : ? -> B . y) else (λz : A -> ? . z)) : Bool -> (A -> B) -> A -> B
example4 = Abstraction "x"
	(If
		(Variable "x")
		(Annotation "y" (ArrowType DynType (ParType "B"))
			(Variable "y"))
		(Annotation "z" (ArrowType (ParType "A") DynType)
			(Variable "z")))

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

-- (λn1 . λn2 . n1 + n2) : Int -> Int -> Int
-- Expression: (abs int x\(abs int y\(add x y)))
-- Compiled: (abs int (W1\ abs int (W2\ add (cast W1 int (_T1 W1 W2) int) (cast W2 int (_T1 W1 W2) int))))
tested_6 = Abstraction "n1" $ Abstraction "n2" $ Addition (Variable "n1") (Variable "n2")

-- (λx : ? . if x then 1 else 2) 1 : Int
-- Expression: (app (abs dyn x\(if x zero zero)) zero)
-- Compiled: (app (cast (abs dyn (W1\ if (cast W1 dyn (_T1 W1) bool) (cast zero int (_T1 W1) int) (cast zero int (_T1 W1) int))) (arrow dyn int) _T2 (arrow dyn int)) (cast zero int _T2 dyn))
tested_7 = Application
	(Annotation "x" DynType $ If (Variable "x") (Int 1) (Int 2))
	(Int 1)

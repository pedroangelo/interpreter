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

-- (λx:? . (λy:X . y) x) : ? -> A
example1 = Annotation "x" DynType
	(Application
		(Annotation "y" (ParType "A") (Variable "y"))
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

-- (\x . x) 1 : Int
-- (app (abs int x\x) (zero))
tested_1 = Application (Abstraction "x" $ Variable "x") (Int 0)

-- (\x : ? . x) 0 : ?
-- (app (abs dyn x\x) (zero))
tested_1_dyn = Application (Annotation "x" DynType $ Variable "x") (Int 0)

-- (\x : Int . 0 + x) True : TypeError
tested_2 = Application (Annotation "x" IntType (Addition (Int 0) (Variable "x"))) (Bool True)
-- (app (abs int (x\(add (zero) x))) (tt))

-- (\x : ? . 0 + x) True : Int
tested_2_dyn = Application (Annotation "x" DynType (Addition (Int 0) (Variable "x"))) (Bool True)
-- (app (abs dyn (x\(add (zero) x))) (tt))

tested_3 = Let "id"
	(Abstraction "x" (Variable "x"))
	(If
		(Application
			(Variable "id")
			(Bool True))
		(Application
			(Variable "id")
			(Int 0))
		(Application
			(Variable "id")
			(Int 0)))

-- let id = (\x . x) in (if (id True) then (id 0) else (id 0)) : ?
tested_3_dyn = Let "id"
	(Annotation "x" DynType (Variable "x"))
	(If
		(Application
			(Variable "id")
			(Bool True))
		(Application
			(Variable "id")
			(Int 0))
		(Application
			(Variable "id")
			(Int 0)))
-- (let (abs dyn x\x) (i\(if (app (i) (tt)) (app (i) (zero)) (app (i) (zero)))))

-- (\id : ? . if (id True) then (id 0) else (id 0)) (\x : ? . x) : ?
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
-- (app (abs dyn id\(if (app id tt) (app id zero) (app id zero))) (abs dyn x\x))

-- (let incr = (\x:? . 1 + x) in incr True) : Int
tested_5_dyn = Let "incr"
	(Annotation "x" DynType $ Addition (Int 1) (Variable "x"))
	(Application (Variable "incr") (Bool True))
-- (let (abs dyn x\(succ(x))) (incr\(app incr tt)))

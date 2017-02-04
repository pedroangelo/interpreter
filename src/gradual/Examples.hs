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

-- let id = (\x . x) in (if (id True) then (id 1) else (id 2)) : Int
example5 = Let "id"
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

-- let t = ((\x . x) True) in (if t then t else t)
example5_1 = Let "id"
	(Application (Abstraction "x" (Variable "x")) (Bool True))
	(If
		(Variable "id")
		(Variable "id")
		(Variable "id"))

-- (let incr = (\x:? . 1 + x) in incr True) : Int
example6 = Let "incr" (Annotation "x" DynType (Addition (Int 1) (Variable "x"))) (Application (Variable "incr") (Bool True))

-- (\x : ? . 1 + x) True : Int
example6_1 = Application (Annotation "x" DynType (Addition (Int 1) (Variable "x"))) (Bool True)

example6_2 = Application (Ascription (Abstraction "x" (Addition (Int 1) (Variable "x"))) (ArrowType DynType IntType)) (Bool True)

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
tested_1 = Application (Annotation "x" IntType $ Variable "x") (Int 0)

-- (λx : ? . x) 0 : ?
tested_1_dyn = Application (Annotation "x" DynType $ Variable "x") (Int 0)

-- (λx : Int . 0 + x) True : TypeError
tested_2 = Application (Annotation "x" IntType (Addition (Int 0) (Variable "x"))) (Bool True)

-- (λx : ? . 0 + x) True : Int
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
tested_5_dyn = Let "incr"
	(Annotation "x" DynType $ Addition (Int 1) (Variable "x"))
	(Application (Variable "incr") (Bool True))

-- (λx : ? . if x then 1 else 2) 1 : Int
tested_6 = Application
	(Annotation "x" DynType $ If (Variable "x") (Int 1) (Int 2))
	(Int 1)

-- (λn1 . λn2 . n1 + n2) : Int -> Int -> Int
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
factorial = LetRec "fact"
	(Abstraction "n" $ If (Equal (Variable "n") (Int 0))
		(Int 1)
		(Multiplication
			(Variable "n")
			(Application
				(Variable "fact")
				(Subtraction (Variable "n") (Int 1)))))
	(Variable "fact")

power_func n p = Application (Application power (Int n)) (Int p)
power = LetRec "power"
	(Abstraction "n" $ Abstraction "p" $ If (Equal (Variable "p") (Int 0))
		(Int 1)
		(Multiplication
			(Variable "n")
			(Application
				(Application (Variable "power") (Variable "n"))
				(Subtraction (Variable "p") (Int 1)))))
	(Variable "power")

moddiv_func m n = Application (Application moddiv (Int m)) (Int n)
moddiv = Abstraction "m" $ Abstraction "n" $
	Let "quotient" (Division (Variable "m") (Variable "n"))
		(Subtraction
			(Variable "m")
			(Multiplication (Variable "n") (Variable "quotient")))

not_func b = Application not' (Bool b)
not' = Abstraction "b" $ If (Variable "b") (Bool False) (Bool True)

gcd_func a b = Application (Application gcd' (Int a)) (Int b)
gcd' = LetRec "gcd"
	(Abstraction "a" $ Abstraction "b" $ If (Equal (Variable "b") (Int 0))
		(Variable "a")
		(Application
			(Application (Variable "gcd") (Variable "b"))
			(Application
				(Application moddiv (Variable "a"))
				(Variable "b"))))
	(Variable "gcd")

absolute = Abstraction "x" $
	If (GreaterEqualTo (Variable "x") (Int 0)) (Variable "x") (Multiplication (Variable "x") (Int (-1)))
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

variants1_err = Application
	(Abstraction "a" $
		CaseVariant (Variable "a")
		[("b", "l", Application (Annotation "z" IntType $ Bool True) (Variable "l")),
		("i", "r", Application (Annotation "z" IntType $ Bool True) (Variable "r"))])
	(Tag "b" (Bool True) (VariantType [("b", BoolType), ("i", IntType)]))

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

variants3 = Application
	(CaseVariant (Tag "ib" (isZero) (VariantType [("ib", ArrowType IntType BoolType)]))
		[("ib", "l", Abstraction "x" $ Application (Variable "l") (Variable "x"))])
	(Int 1)

variants3_dyn = CaseVariant (Tag "ib" (isZero) (VariantType [("ib", DynType)]))
	[("ib", "l", Abstraction "x" $ Application (Variable "l") (Variable "x"))]

records1 = Projection "b" (Record [("b", Bool True)]) (RecordType [("b", BoolType)])

records1_dyn = Projection "b" (Record [("b", Bool True)]) (RecordType [("b", DynType)])

records2 = Application
	(Abstraction "x" $ Projection "b" (Variable "x") (RecordType [("b", DynType)]))
	(Record [("b", Bool True)])

records2_dyn = Application
	(Annotation "x" DynType $ Projection "b" (Variable "x") (RecordType [("b", DynType)]))
	(Record [("b", Bool True)])

records3 = Projection "1" (Application
	(Abstraction "x" $ If (Projection "1" (Variable "x") (RecordType [("1", BoolType), ("2", IntType)])) (Variable "x") (Variable "x"))
	(Record [("1", Bool True), ("2", Int 1)])) (RecordType [("1", BoolType), ("2", IntType)])

records3_dyn = Projection "1" (Application
	(Annotation "x" DynType $ If (Projection "1" (Variable "x") (RecordType [("1", BoolType), ("2", IntType)])) (Variable "x") (Variable "x"))
	(Record [("1", Bool True), ("2", Int 1)])) (RecordType [("1", BoolType), ("2", IntType)])

-- Data

posType = RecordType [("x", IntType), ("y", IntType)]
squareType = RecordType [("topleft", posType), ("bottomright", posType)]
circleType = RecordType [("center", posType), ("radius", IntType)]
triangleType = RecordType [("p1", posType), ("p2", posType), ("p3", posType)]
shapeType = VariantType
	[("Square", squareType),
	("Circle", circleType),
	("Triangle", triangleType)]

buildPos_func x y = Application (Application buildPos (Int x)) (Int y)
buildPos = Abstraction "x" $ Abstraction "y" $
	Record [("x", Variable "x"), ("y", Variable "y")]

buildSquare_func p1 p2 = Application (Application buildSquare p1) p2
buildSquare = Abstraction "tl" $ Abstraction "br" $
	Tag "Square" (Record [("topleft", Variable "tl"), ("bottomright", Variable "br")]) shapeType

square1 = buildSquare_func (buildPos_func 3 5) (buildPos_func 5 3)

buildCircle_func c r = Application (Application buildCircle c) r
buildCircle = Abstraction "c" $ Abstraction "r" $
	Tag "Circle" (Record [("center", Variable "c"), ("radius", Variable "r")]) shapeType

circle1 = buildCircle_func (buildPos_func 2 2) (Int 2)

buildTriangle_func p1 p2 p3 = Application (Application (Application buildTriangle p1) p2) p3
buildTriangle = Abstraction "p1" $ Abstraction "p2" $ Abstraction "p3" $
	Tag "Triangle" (Record [("p1", Variable "p1"), ("p2", Variable "p2"), ("p3", Variable "p3")]) shapeType

triangle1 = buildTriangle_func (buildPos_func 7 5) (buildPos_func 8 3) (buildPos_func 6 3)

calculateCenterSquare = Abstraction "square" $
	Let "topleft" (Projection "topleft" (Variable "square") squareType) $
	Let "bottomright" (Projection "bottomright" (Variable "square") squareType) $
	Let "topleftx" (Projection "x" (Variable "topleft") posType) $
	Let "toplefty" (Projection "y" (Variable "topleft") posType) $
	Let "bottomrightx" (Projection "x" (Variable "bottomright") posType) $
	Let "bottomrighty" (Projection "y" (Variable "bottomright") posType) $
	Application (Application (buildPos)
		(Division (Addition (Variable "bottomrightx") (Variable "topleftx")) (Int 2)))
		(Division (Addition (Variable "toplefty") (Variable "bottomrighty")) (Int 2))

calculateCenterCircle = Abstraction "circle" $
	Projection "center" (Variable "circle") circleType

calculateCenterTriangle = Abstraction "triangle" $
	Let "p1" (Projection "p1" (Variable "triangle") triangleType) $
	Let "p2" (Projection "p2" (Variable "triangle") triangleType) $
	Let "p3" (Projection "p3" (Variable "triangle") triangleType) $
	Let "x" (Division
		(Addition
			(Projection "x" (Variable "p1") posType)
			(Addition
				(Projection "x" (Variable "p2") posType)
				(Projection "x" (Variable "p3") posType))) (Int 3)) $
	Let "y" (Division
		(Addition
			(Projection "y" (Variable "p1") posType)
			(Addition
				(Projection "y" (Variable "p2") posType)
				(Projection "y" (Variable "p3") posType))) (Int 3)) $
	Application (Application buildPos (Variable "x")) (Variable "y")

calculateCenter = Abstraction "shape" $
	CaseVariant (Variable "shape")
		[("Square", "s", Application calculateCenterSquare (Variable "s")),
		("Circle", "c", Application calculateCenterCircle (Variable "c")),
		("Triangle", "t", Application calculateCenterTriangle (Variable "t"))]

-- Recursive Types

-- List of Int
intList = Mu "L" $ SumType (UnitType) (ProductType IntType (VarType "L"))
intList' = unfoldType ("L", intList) intList

nil = Fold intList $ LeftTag Unit intList'

cons = Abstraction "n" $ Abstraction "l" $
	Fold intList $ RightTag (Pair (Variable "n") (Variable "l")) intList'

isnil = Abstraction "l" $ Case (Unfold intList $ Variable "l")
	("x", Bool True)
	("x", Bool False)

hd = Abstraction "l" $ Case (Unfold intList $ Variable "l")
	("x", (Error "*** Exception: empty list"))
	("x", First $ Variable "x")

tl = Abstraction "l" $ Case (Unfold intList $ Variable "l")
	("x", (Error "*** Exception: empty list"))
	("x", Second $ Variable "x")

list1 = Application (Application cons (Int 1)) nil

list2 = Application (Application cons (Int 2)) list1

sumlist = Fix $ Abstraction "s" $ Abstraction "l" $
	If (Application (isnil) (Variable "l"))
		(Int 0)
		(Addition
			(Application (hd) (Variable "l"))
			(Application
				(Variable "s")
				(Application (tl) (Variable "l"))))

mapInt = Fix $ Abstraction "m" $ Abstraction "f" $ Abstraction "l" $
	If (Application isnil (Variable "l"))
		nil
		(Application
			(Application
				(cons)
				(Application
					(Variable "f")
					(Application (hd) (Variable "l"))))
			(Application
				(Application (Variable "m") (Variable "f"))
				(Application (tl) (Variable "l"))))

map_func f l =  Application (Application (mapInt) f) l

-- Ordering

orderingType = VariantType [("LT", UnitType), ("EQ", UnitType), ("GT", UnitType)]

compare_func x y = Application (Application compare' x) (y)

compare' = Abstraction "x" $ Abstraction "y" $
	If (Equal (Variable "x") (Variable "y"))
		(Tag "EQ" Unit orderingType)
		(If (LesserThan (Variable "x") (Variable "y"))
			(Tag "LT" Unit orderingType)
			(Tag "GT" Unit orderingType))
-- Trees of ints

treeType = Mu "T" $ VariantType
	[("Leaf", UnitType),
	("Node", RecordType
		[("Value", IntType),
		("Left", VarType "T"),
		("Right", VarType "T")])]

nodeType = RecordType
	[("Value", IntType),
	("Left", treeType),
	("Right", treeType)]

treeType' = unfoldType ("T", treeType) treeType

emptyTree = Fold treeType $ Tag "Leaf" Unit treeType'

tree1 = Fold treeType $ Tag "Node"
	(Record
		[("Value", Int 1),
		("Left", emptyTree ),
		("Right", emptyTree )]) treeType'

tree12 = Application (Application insertTree (Int 2)) (tree1)

tree123 = Application (Application insertTree (Int 3)) (tree12)

getNumberNode = Abstraction "node" $ Projection "Value" (Variable "node") nodeType

getLeftSide = Abstraction "node" $ Projection "Left" (Variable "node") nodeType

getRightSide = Abstraction "node" $ Projection "Right" (Variable "node") nodeType

sizeTree = Fix $ Abstraction "s" $ Abstraction "t" $
	CaseVariant (Unfold treeType $ Variable "t")
		[("Leaf", "", Int 0),
		("Node", "x", Addition (Int 1)
			(Addition
				(Application (Variable "s") (Projection "Left" (Variable "x") nodeType ))
				(Application (Variable "s") (Projection "Right" (Variable "x") nodeType ))))]

insertTree = Fix $ Abstraction "insertTree" $ Abstraction "i" $ Abstraction "t" $
	CaseVariant (Unfold treeType $ Variable "t")
		[("Leaf", "leaf", Fold treeType $
			Tag "Node" (Record
				[("Value", Variable "i"),
				("Left", emptyTree),
				("Right", emptyTree)]) treeType'),
		("Node", "node", Let "num" (Application getNumberNode (Variable "node")) $
			CaseVariant (compare_func (Variable "i") (Variable "num"))
				[("LT", "", Fold treeType $
					Tag "Node" (Record
						[("Value", Variable "num"),
						("Left", Let "l" (Application getLeftSide (Variable "node")) $
							Application (Application (Variable "insertTree") (Variable "i")) (Variable "l")),
						("Right", Application getRightSide (Variable "node"))]) treeType'),
				("EQ", "", Fold treeType $
					Tag "Node" (Record
						[("Value", Variable "num"),
						("Left", Application getLeftSide (Variable "node")),
						("Right", Application getRightSide (Variable "node"))]) treeType'),
				("GT", "", Fold treeType $
					Tag "Node" (Record
						[("Value", Variable "num"),
						("Left", Application getLeftSide (Variable "node")),
						("Right", Let "r" (Application getRightSide (Variable "node")) $
							Application (Application (Variable "insertTree") (Variable "i")) (Variable "r"))]) treeType')])]

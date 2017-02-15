module CastInsertion (
	insertCasts
) where

-- Syntax & Types
import Syntax
import Types

-- insert casts in the expression
insertCasts :: Expression -> Expression

-- if expression is a value
insertCasts e@(TypeInformation _ (Variable _)) = e

-- if expression is an abstraction
insertCasts e@(TypeInformation typ (Abstraction var expr)) =
	TypeInformation typ $ Abstraction var $ insertCasts expr

-- if expression is an application
insertCasts e@(TypeInformation typ (Application expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- buid types
		t1 = getType expr1'
		t2 = getType expr2'
		d1 = patternMatch t1 ArrowT
		ArrowType d2 t = d1
		-- build casts
		cast1 = Cast t1 d1 expr1'
		cast2 = Cast t2 d2 expr2'
	in TypeInformation t $ Application cast1 cast2

-- if expression is an ascription
insertCasts e@(TypeInformation typ (Ascription expr typ')) =
	TypeInformation typ $ Ascription (insertCasts expr) typ'

-- if expression is an annotation
insertCasts e@(TypeInformation typ (Annotation var annotation expr)) =
	TypeInformation typ $ Annotation var annotation $ insertCasts expr

-- if expression is a integer
insertCasts e@(TypeInformation _ (Int _)) = e

-- if expression is a boolean
insertCasts e@(TypeInformation _ (Bool _)) = e

-- if expression is a let binding
insertCasts e@(TypeInformation typ (Let var expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
	in TypeInformation typ $ Let var expr1' expr2'

-- if expression is a fixed point operator
insertCasts e@(TypeInformation typ (Fix expr)) =
	let
		-- insert casts
		expr' = insertCasts expr
		-- build types
		t = getType expr'
		p = patternMatch t ArrowT
		ArrowType d _ = p
		-- build casts
		cast = Cast t (ArrowType d d) expr'
	in TypeInformation t $ Fix cast

-- if expression is a recursive let binding
insertCasts e@(TypeInformation typ (LetRec var expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		t1 = getType expr1
		t1' = getType expr1'
		t2 = getType expr2'
		-- build casts
		cast = Cast t1' t1 expr1'
	in TypeInformation t2 $ LetRec var cast expr2'

-- if expression is a conditional statement
insertCasts e@(TypeInformation typ (If expr1 expr2 expr3)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		expr3' = insertCasts expr3
		-- build types
		t1 = getType expr1'
		t2 = getType expr2'
		t3 = getType expr3'
		d = joinType t2 t3
		-- build casts
		cast1 = Cast t1 BoolType expr1'
		cast2 = Cast t2 d expr2'
		cast3 = Cast t3 d expr3'
	in TypeInformation d $ If cast1 cast2 cast3

-- if expression is an addition
insertCasts e@(TypeInformation typ (Addition expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		t1 = getType expr1'
		t2 = getType expr2'
		-- build casts
		cast1 = Cast t1 IntType expr1'
		cast2 = Cast t2 IntType expr2'
	in TypeInformation IntType $ Addition cast1 cast2

-- if expression is a subtraction
insertCasts e@(TypeInformation typ (Subtraction expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		t1 = getType expr1'
		t2 = getType expr2'
		-- build casts
		cast1 = Cast t1 IntType expr1'
		cast2 = Cast t2 IntType expr2'
	in TypeInformation IntType $ Subtraction cast1 cast2

-- if expression is a multiplication
insertCasts e@(TypeInformation typ (Multiplication expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		t1 = getType expr1'
		t2 = getType expr2'
		-- build casts
		cast1 = Cast t1 IntType expr1'
		cast2 = Cast t2 IntType expr2'
	in TypeInformation IntType $ Multiplication cast1 cast2

-- if expression is a division
insertCasts e@(TypeInformation typ (Division expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		t1 = getType expr1'
		t2 = getType expr2'
		-- build casts
		cast1 = Cast t1 IntType expr1'
		cast2 = Cast t2 IntType expr2'
	in TypeInformation IntType $ Division cast1 cast2

-- if expression is a equality check
insertCasts e@(TypeInformation typ (Equal expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		t1 = getType expr1'
		t2 = getType expr2'
		-- build casts
		cast1 = Cast t1 IntType expr1'
		cast2 = Cast t2 IntType expr2'
	in TypeInformation BoolType $ Equal cast1 cast2

-- if expression is a non equality check
insertCasts e@(TypeInformation typ (NotEqual expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		t1 = getType expr1'
		t2 = getType expr2'
		-- build casts
		cast1 = Cast t1 IntType expr1'
		cast2 = Cast t2 IntType expr2'
	in TypeInformation BoolType $ NotEqual cast1 cast2

-- if expression is a lesser than check
insertCasts e@(TypeInformation typ (LesserThan expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		t1 = getType expr1'
		t2 = getType expr2'
		-- build casts
		cast1 = Cast t1 IntType expr1'
		cast2 = Cast t2 IntType expr2'
	in TypeInformation BoolType $ LesserThan cast1 cast2

-- if expression is a greater than check
insertCasts e@(TypeInformation typ (GreaterThan expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		t1 = getType expr1'
		t2 = getType expr2'
		-- build casts
		cast1 = Cast t1 IntType expr1'
		cast2 = Cast t2 IntType expr2'
	in TypeInformation BoolType $ GreaterThan cast1 cast2

-- if expression is a lesser than or equal to check
insertCasts e@(TypeInformation typ (LesserEqualTo expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		t1 = getType expr1'
		t2 = getType expr2'
		-- build casts
		cast1 = Cast t1 IntType expr1'
		cast2 = Cast t2 IntType expr2'
	in TypeInformation BoolType $ LesserEqualTo cast1 cast2

-- if expression is a greater than or equal to check
insertCasts e@(TypeInformation typ (GreaterEqualTo expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		t1 = getType expr1'
		t2 = getType expr2'
		-- build casts
		cast1 = Cast t1 IntType expr1'
		cast2 = Cast t2 IntType expr2'
	in TypeInformation BoolType $ GreaterEqualTo cast1 cast2

-- get type information
getType :: Expression -> Type
getType (TypeInformation typ _) = typ

data TypeTemplate
	= ArrowT

-- obtain pattern match type
patternMatch :: Type -> TypeTemplate -> Type
patternMatch e@(ArrowType type1 type2) ArrowT = e
patternMatch e@(DynType) ArrowT = ArrowType DynType DynType

-- obtain join of types
joinType :: Type -> Type -> Type
joinType (ArrowType t11 t12) (ArrowType t21 t22) =
	let
		t1 = joinType t11 t21
		t2 = joinType t12 t22
	in ArrowType t1 t2
joinType t1 t2
	| not (isArrowType t1) && not (isArrowType t2) =
		if (isDynType t1) then t2 else t1

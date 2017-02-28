module Evaluation (
	evaluate
) where

-- Syntax & Types
import Syntax
import Types
import Examples

-- evaluate using call-by-value strategy
evaluate :: Expression -> Expression

-- variables are values
evaluate e@(Variable _) = e

-- abstractions are values
evaluate e@(Abstraction _ _) = e

-- if expression is an application
evaluate e@(Application expr1 expr2)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ Application v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ Application expr1 v2
	-- C-BETA - simulate casts on data types
	| isCast expr1 =
		let
			(Cast t1 t2 expr1') = expr1
			(ArrowType t11 t12) = t1
			(ArrowType t21 t22) = t2
			expr2' = Cast t21 t11 expr2
		in evaluate $ Cast t12 t22 $ Application expr1' expr2'
	-- beta reduction
	| isAbstraction expr1 && isValue expr2 =
		let (Abstraction var expr) = expr1
		in evaluate $ substitute (var, expr2) expr

-- if expression is an ascription
evaluate e@(Ascription expr typ)
	-- push blames to top level
	| isBlame expr = expr
	-- remove ascription
	| isValue expr = evaluate $ expr
	| otherwise =
		let v1 = evaluate expr
		in evaluate $ Ascription v1 typ

-- if expression is an annotated abstraction
evaluate e@(Annotation var typ expr) =
	-- remove type
	Abstraction var expr

-- booleans are values
evaluate e@(Bool _) = e

-- integers are values
evaluate e@(Int _) = e

-- if expression is let binding
evaluate e@(Let var expr1 expr2)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ Let var v1 expr2
	-- substitute ocurrences of var in expr2 by expr1
	| otherwise = evaluate $ substitute (var, expr1) expr2

-- if expression is fixed point
evaluate e@(Fix expr)
	-- push blames to top level
	| isBlame expr = expr
	-- reduce expr
	| not $ isValue expr =
		let v = evaluate expr
		in evaluate $ Fix v
	-- substitute abstraction variable with e in expr
	| isAbstraction expr =
		let (Abstraction var expr') = expr
		in evaluate $ substitute (var, e) expr'

-- if expression is a recursive let binding
evaluate e@(LetRec var expr1 expr2) =
	-- derive form into a let binding
	evaluate $ Let var (Fix $ Abstraction var expr1) expr2

-- if expression is a conditional statement
evaluate e@(If expr1 expr2 expr3)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	| isBlame expr3 = expr3
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ If v1 expr2 expr3
	-- if expr1 is True, evaluate expr2
	| expr1 == Bool True = evaluate expr2
	--- if expr1 is False, evaluate expr3
	| expr1 == Bool False = evaluate expr3

-- if expression is a addition
evaluate e@(Addition expr1 expr2)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ Addition v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ Addition expr1 v2
	-- call native addition function between expr1 and expr2
	| otherwise =
		let
			Int i1 = expr1
			Int i2 = expr2
		in Int (i1 + i2)

-- if expression is a subtraction
evaluate e@(Subtraction expr1 expr2)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ Subtraction v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ Subtraction expr1 v2
	-- call native subtraction function between expr1 and expr2
	| otherwise =
		let
			Int i1 = expr1
			Int i2 = expr2
		in Int (i1 - i2)

-- if expression is a multiplication
evaluate e@(Multiplication expr1 expr2)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ Multiplication v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ Multiplication expr1 v2
	-- call native multiplication function between expr1 and expr2
	| otherwise =
		let
			Int i1 = expr1
			Int i2 = expr2
		in Int (i1 * i2)

-- if expression is a division
evaluate e@(Division expr1 expr2)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ Division v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ Division expr1 v2
	-- call native division function between expr1 and expr2
	| otherwise =
		let
			Int i1 = expr1
			Int i2 = expr2
		in Int $ div i1 i2

-- if expression is a equality check
evaluate e@(Equal expr1 expr2)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ Equal v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ Equal expr1 v2
	-- call native equality check between expr1 and expr2
	| otherwise =
		let
			Int i1 = expr1
			Int i2 = expr2
		in Bool (i1 == i2)

-- if expression is a non equality check
evaluate e@(NotEqual expr1 expr2)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ NotEqual v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ NotEqual expr1 v2
	-- call native non equality check between expr1 and expr2
	| otherwise =
		let
			Int i1 = expr1
			Int i2 = expr2
		in Bool (i1 /= i2)

-- if expression is a lesser than check
evaluate e@(LesserThan expr1 expr2)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ LesserThan v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ LesserThan expr1 v2
	-- call native lesser than check between expr1 and expr2
	| otherwise =
		let
			Int i1 = expr1
			Int i2 = expr2
		in Bool (i1 < i2)

-- if expression is a greater than check
evaluate e@(GreaterThan expr1 expr2)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ GreaterThan v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ GreaterThan expr1 v2
	-- call native greater than check between expr1 and expr2
	| otherwise =
		let
			Int i1 = expr1
			Int i2 = expr2
		in Bool (i1 > i2)

-- if expression is a lesser than or equal to check
evaluate e@(LesserEqualTo expr1 expr2)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ LesserEqualTo v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ LesserEqualTo expr1 v2
	-- call native lesser than or equal to check between expr1 and expr2
	| otherwise =
		let
			Int i1 = expr1
			Int i2 = expr2
		in Bool (i1 <= i2)

-- if expression is a greater than or equal to check
evaluate e@(GreaterEqualTo expr1 expr2)
	-- push blames to top level
	| isBlame expr1 = expr1
	| isBlame expr2 = expr2
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ GreaterEqualTo v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ GreaterEqualTo expr1 v2
	-- call native greater than or equal to check between expr1 and expr2
	| otherwise =
		let
			Int i1 = expr1
			Int i2 = expr2
		in Bool (i1 >= i2)

-- if expression is a type information
evaluate e@(TypeInformation typ expr) = expr

-- if expression is a cast
evaluate e@(Cast t1 t2 expr)
	-- push blame to top level
	| isBlame expr = expr
	-- values don't reduce
	| isValue e = e
	-- evaluate inside a cast
	| (not $ isValue expr) =
		let expr2 = evaluate expr
		in evaluate $ Cast t1 t2 expr2
	-- ID-BASE - remove casts to same types
	| isValue expr && t1 == t2 = evaluate expr
	-- SUCCEED - cast is sucessful
	| isCast expr && t1 == DynType && t2' == DynType &&	isGroundType t2 && t1' == t2 =
			evaluate expr'
	-- FAIL - cast fails
	| isCast expr && t1 == DynType && t2' == DynType &&
		isGroundType t2 && isGroundType t1' && (not $ sameGround t1' t2) =
			Blame t2 $ "cannot cast from " ++ (show t1') ++ " to " ++ (show t2)
	-- GROUND - cast types through their ground types
	| (not $ isGroundType t1) && t2 == DynType =
		let g = getGroundType t1
		in evaluate $ Cast g DynType $ Cast t1 g expr
	-- EXPAND - cast types through their ground types
	| (not $ isGroundType t2) && t1 == DynType =
		let g = getGroundType t2
		in evaluate $ Cast g t2 $ Cast DynType g expr
	-- Project types and expression from inner casts
	where
		(Cast t1' t2' expr') = expr

-- if expression is a blame label
evaluate e@(Blame t label) = e

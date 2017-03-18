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
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ Application v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ Application expr1 v2
	-- beta reduce e
	| isAbstraction expr1 && isValue expr2 =
		let (Abstraction var expr) = expr1
		in evaluate $ substitute (var, expr2) expr

-- if expression is an ascription
evaluate e@(Ascription expr typ)
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
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ Let var v1 expr2
	-- substitute ocurrences of var in expr2 by expr1
	| otherwise = evaluate $ substitute (var, expr1) expr2

-- if expression is fixed point
evaluate e@(Fix expr)
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

-- if expression is an unit
evaluate e@(Unit) = e

-- if expression is a pair
evaluate e@(Pair expr1 expr2)
	-- reduce expr1
	| not $ isValue expr1 =
		let v1 = evaluate expr1
		in evaluate $ Pair v1 expr2
	-- reduce expr2
	| not $ isValue expr2 =
		let v2 = evaluate expr2
		in evaluate $ Pair expr1 v2
	| otherwise = e

-- if expression is a first projection
evaluate e@(First expr)
	-- reduce expr
	| not $ isValue expr =
		let v = evaluate expr
		in evaluate $ First v
	-- project first element of pair
	| isPair expr =
		let (Pair expr1 expr2) = expr
		in evaluate $ expr1

-- if expression is a second projection
evaluate e@(Second expr)
	-- reduce expr
	| not $ isValue expr =
		let v = evaluate expr
		in evaluate $ Second v
	-- project first element of pair
	| isPair expr =
		let (Pair expr1 expr2) = expr
			in evaluate $ expr2

-- if expression is a record
evaluate e@(Record records)
	-- reduce expressions
	| any (not . isValue) exprs =
		let exprs' = map evaluate exprs
		in Record $ zip labels exprs'
	| otherwise = e
	where (labels, exprs) = fromRecords records

-- if expression is a projection
evaluate e@(Projection label expr typ)
	-- reduce expr
	| not $ isValue expr =
		let v = evaluate expr
		in evaluate $ Projection label v typ
	-- project element of record
	| isRecord expr =
		let
			Record list = expr
			Just expr' = lookup label list
		in evaluate expr'

-- if expression is a case
evaluate e@(Case expr (var1, expr1) (var2, expr2))
	-- reduce expr
	| not $ isValue expr =
		let v = evaluate expr
		in evaluate $ Case v (var1, expr1) (var2, expr2)
	-- if is left tag
	| isLeftTag expr =
		let (LeftTag exprl typ) = expr
		in evaluate $ substitute (var1, exprl) expr1
	-- if is right tag
	| isRightTag expr =
		let (RightTag exprr typ) = expr
		in evaluate $ substitute (var2, exprr) expr2

-- if expression is a right tag
evaluate e@(LeftTag expr typ)
	-- reduce expr
	| not $ isValue expr =
		let v = evaluate expr
		in LeftTag v typ
	| otherwise = e

-- if expression is a right tag
evaluate e@(RightTag expr typ)
	-- reduce expr
	| not $ isValue expr =
		let v = evaluate expr
		in RightTag v typ
	| otherwise = e

-- if expression is a variant case
evaluate e@(CaseVariant expr alternatives)
	-- reduce expr
	| not $ isValue expr =
		let v = evaluate expr
		in evaluate $ CaseVariant v alternatives
	-- if is tag
	| isTag expr =
		let
			(Tag label expr' _) = expr
			-- obtain correct alternative according to label
			(_, var, alternative) =
				head $ filter (\x -> label == (fst3 x)) alternatives
		in evaluate $ substitute (var, expr') alternative

-- if expressions is a tag
evaluate e@(Tag label expr typ)
	-- reduce expr
	| not $ isValue expr =
		let v = evaluate expr
		in Tag label v typ
	| otherwise = e

-- if expression is a fold
evaluate e@(Fold typ expr)
	-- reduce expr
	| not $ isValue expr =
		let v = evaluate expr
		in Fold typ v
	| otherwise = e

-- if expression is a fold
evaluate e@(Unfold typ expr)
	-- reduce expr
	| not $ isValue expr =
		let v = evaluate expr
		in Unfold typ v
	-- if expression is an unfold of a fold
	| isFold expr =
		let (Fold _ expr') = expr
		in expr'

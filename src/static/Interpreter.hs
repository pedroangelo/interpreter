module Interpreter where

-- Syntax
import Syntax
import Examples

-- evaluate using call-by-name strategy
evaluate :: Expression -> Expression
-- variables are values
evaluate e@(Variable _) = e
-- abstractions are values
evaluate e@(Abstraction _ _) = e
-- if expression is application
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
	| otherwise = Error "Application: expression not compatible"
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
		in substitute (var, e) expr'
	| otherwise = Error "Fix: expression not compatible"
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
	| otherwise = Error "If: expression not compatible"
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

type Substitution = (String, Expression)

-- Substitute expressions according to substitution
substitute :: Substitution -> Expression -> Expression
-- if the expression is a variable
substitute s@(old, new) e@(Variable var)
	-- if var equals old, replace variable with new expression
	| var == old = new
	-- otherwise, replace nothing
	| otherwise = e
-- if the expression is a abstraction
substitute s@(old, new) e@(Abstraction var expr)
	-- if abstractions has already binded the variable, don't propagate substitutions
	| var == old = e
	-- otherwise, propagate substitutions
	| otherwise = Abstraction var $ substitute s expr
-- if the expression is a application
substitute s@(old, new) e@(Application expr1 expr2) =
	-- propagate substitutions
	Application (substitute s expr1) (substitute s expr2)
-- if the expression is a base type such as Int or Bool, do nothing
substitute s@(old, new) e@(Bool _) = e
substitute s@(old, new) e@(Int _) = e
-- if the expression is a let binding
substitute s@(old, new) e@(Let var expr1 expr2)
	-- if let has already binded the variable, dont propagate substitutions
	| var == old = e
	-- otherwise, propagate substitutions
	| otherwise = Let var (substitute s expr1) (substitute s expr2)
-- if the expression is a fixed point, propagate substitutions
substitute s@(old, new) e@(Fix expr) = Fix $ substitute s expr
-- if the expression is a recursive let binding
substitute s@(old, new) e@(LetRec var expr1 expr2)
	-- if let has already binded the variable, dont propagate substitutions
	| var == old = e
	-- otherwise, propagate substitutions
	| otherwise = LetRec var (substitute s expr1) (substitute s expr2)
-- if the expression is a conditional statement
substitute s@(old, new) e@(If expr1 expr2 expr3) =
	-- propagate substitutions
	If (substitute s expr1) (substitute s expr2) (substitute s expr3)
-- if expression is a arithmetic operation or comparison operator,
-- propagate substitutions
substitute s@(old, new) e@(Addition expr1 expr2) =
	Addition (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(Subtraction expr1 expr2) =
	Subtraction (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(Multiplication expr1 expr2) =
	Multiplication (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(Division expr1 expr2) =
	Division (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(Equal expr1 expr2) =
	Equal (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(NotEqual expr1 expr2) =
	NotEqual (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(LesserThan expr1 expr2) =
	LesserThan (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(GreaterThan expr1 expr2) =
	GreaterThan (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(LesserEqualTo expr1 expr2) =
	LesserEqualTo (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(GreaterEqualTo expr1 expr2) =
	GreaterEqualTo (substitute s expr1) (substitute s expr2)

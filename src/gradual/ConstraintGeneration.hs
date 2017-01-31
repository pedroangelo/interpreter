module ConstraintGeneration (
	generateConstraints
) where

-- Syntax & Types
import Syntax
import Types

-- Imports
import Control.Monad.State
import Data.Maybe

-- generate constraint set and type given a context and expression
generateConstraints :: (Context, Expression) -> State Int (Type, Constraints)

-- (Cx) if expression is a variable
generateConstraints (ctx, Variable var) = do
	-- obtain type from context
	let result = lookup var ctx
	-- return type
	return (fromJust result, [])

-- (Cλ) if expression is a abstraction
generateConstraints (ctx, Abstraction var expr) = do
	-- counter for variable creation
	i <- get
	put (i+1)
	-- create new type variable
	let newVar1 = newTypeVar i
	-- create a binding between the abstraction variable and the new type variable
	let binding = (var, newVar1)
	-- build type assignment with new binding
	let typeAssignment = (binding : ctx, expr)
	-- obtain type and generate constraints for new type assignment
	(exprType, constraints) <- generateConstraints typeAssignment
	-- return arrow type and constraints
	return (ArrowType newVar1 exprType, constraints)

-- (Capp) if expression is a application
generateConstraints (ctx, Application expr1 expr2) = do
	-- build for each expression in the application
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	-- get constraints for codomain and domain relation
	(t3, constraints3) <- codomain t1
	constraints4 <- domain t1 t2
	-- return type along with all the constraints
	return (t3, constraints1 ++ constraints2 ++ constraints3 ++ constraints4)

-- (C::) if expression is an ascription
generateConstraints (ctx, Ascription expr typ) = do
	-- build type assignment for expression
	let typeAssignment = (ctx, expr)
	-- obtain type and generate constraints for type assignment
	(exprType, constraints) <- generateConstraints typeAssignment
	-- return type along with all the constraints
	return (typ, constraints ++ [Consistency exprType typ])

-- (Cλ:) if expression is a annotated abstraction
generateConstraints (ctx, Annotation var typ expr) = do
	-- create a binding between the abstraction variable and the annotated type
	let binding = (var, typ)
	-- build type assignment with new binding
	let typeAssignment = (binding : ctx, expr)
	-- obtain type and generate constraints for new type assignment
	(exprType, constraints) <- generateConstraints typeAssignment
	-- return arrow type and constraints
	return (ArrowType typ exprType, constraints)

-- (Cn) if expression is a integer
generateConstraints (ctx, Int int) = do
	-- return Int type
	return (IntType, [])

-- (Cb) if expression is a boolean
generateConstraints (ctx, Bool bool) = do
	-- return Bool type
	return (BoolType, [])

-- if expression is a let binding
generateConstraints (ctx, Let var expr1 expr2)
	-- (Cletp) if expression is a let binding a value to a variable
	| isValue expr1 = do
		-- build type assignment for value
		let typeAssignment1 = (ctx, expr1)
		-- obtain type and generate constraints for type assignment
		(t1, constraints1) <- generateConstraints typeAssignment1
		-- build type assignment for value
		let typeAssignment2 = (ctx, substitute (var, expr1) expr2)
		-- obtain type and generate constraints for type assignment
		(t2, constraints2) <- generateConstraints typeAssignment2
		-- return type along with all the constraints
		return (t2, constraints1 ++ constraints2)
	-- (Clet) if expression is a let binding a expression to a variable
	| otherwise = do
		-- build type assignment for expression
		let typeAssignment = (ctx, Application (Abstraction var expr2) (expr1))
		-- obtain type and generate constraints for type assignment
		(exprType, constraints) <- generateConstraints typeAssignment
		-- return type along with all the constraints
		return (exprType, constraints)

-- if expression is a fixed point
generateConstraints (ctx, Fix expr) = do
	-- counter for variable creation
	i <- get
	put (i+2)
	-- create new type variable
	let newVar1 = newTypeVar i
	let newVar2 = newTypeVar (i+1)
	-- build type assignment
	let typeAssignment1 = (ctx, expr)
	-- obtain type and generate constraints for type assignment
	(t1, constraints) <- generateConstraints typeAssignment1
	return (newVar1, constraints ++ [Consistency t1 (ArrowType newVar1 newVar2)])

-- if expression is a recursive let binding
generateConstraints (ctx, LetRec var expr1 expr2) = do
	-- build type assignment
	let typeAssignment = (ctx, Let var (Fix $ Abstraction var expr1) expr2)
	-- obtain type and generate constraints for type assignment
	(t, constraints) <- generateConstraints typeAssignment
	return (t, constraints)

-- (Cif) if expression if a conditional statement
generateConstraints (ctx, If expr1 expr2 expr3) = do
	-- build for each expression in the application
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	let typeAssignment3 = (ctx, expr3)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	(t3, constraints3) <- generateConstraints typeAssignment3
	let (t4, constraints4) = meet t2 t3
	-- return type along with all the constraints
	return (t4, constraints1 ++ constraints2 ++ constraints3 ++ constraints4 ++ [Consistency t1 BoolType])

-- (C+) if expression if an addition
generateConstraints (ctx, Addition expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	-- return type along with all the constraints
	return (IntType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType])

-- (C-) if expression if a subtraction
generateConstraints (ctx, Subtraction expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	-- return type along with all the constraints
	return (IntType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType])

-- (C*) if expression if a multiplication
generateConstraints (ctx, Multiplication expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	-- return type along with all the constraints
	return (IntType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType])

-- (C/) if expression if a division
generateConstraints (ctx, Division expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	-- return type along with all the constraints
	return (IntType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType])

-- (C==) if expression if a equality check
generateConstraints (ctx, Equal expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	-- return type along with all the constraints
	return (BoolType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType])

-- (C/=) if expression if a not equality check
generateConstraints (ctx, NotEqual expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	-- return type along with all the constraints
	return (BoolType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType])

-- (C<) if expression if a lesser than check
generateConstraints (ctx, LesserThan expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	-- return type along with all the constraints
	return (BoolType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType])

-- (C>) if expression if a greater than check
generateConstraints (ctx, GreaterThan expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	-- return type along with all the constraints
	return (BoolType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType])

-- (C<=) if expression if a lesser than or equal to check
generateConstraints (ctx, LesserEqualTo expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	-- return type along with all the constraints
	return (BoolType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType])

-- (C>=) if expression if a greater than or equal to
generateConstraints (ctx, GreaterEqualTo expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	-- return type along with all the constraints
	return (BoolType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType])

-- generate constraints and type for codomain relation
codomain :: Type -> State Int (Type, Constraints)
codomain t
	-- if t is type variable
	| isVarType t = do
		-- create two new type variables t1 and t2
		i <- get
		put (i+2)
		let t1 = newTypeVar i
		let t2 = newTypeVar (i+1)
		-- return as type t2 and equality relation t =
		return (t2, [Equality t (ArrowType t1 t2)])
	-- if t is arrow type
	| isArrowType t = do
		-- let t1 and t2 such that t = t1 -> t2
		let (ArrowType t1 t2) = t
		-- return as type t2
		return (t2, [])
	-- if t is dynamic type
	| isDynType t = do
		-- return dynamic typ
		return (DynType, [])
-- generate constraints for domain relation
domain :: Type -> Type -> State Int Constraints
domain t1 t2
	-- if t1 is type variable
	| isVarType t1 = do
		-- create two new type variables t11 and t12
		i <- get
		put (i+2)
		let t11 = newTypeVar i
		let t12 = newTypeVar (i+1)
		-- return constraints t11 ~C t2 and t1 =C t11 -> t12
		return [Consistency t11 t2, Equality t1 (ArrowType t11 t12)]
	-- if t1 is arrow type
	| isArrowType t1 = do
		-- let t11 and t12 such that t1 = t11 -> t12
		let (ArrowType t11 t12) = t1
		-- return constraints t11 ~C t2
		return [Consistency t11 t2]
	-- if t1 is dynamic type
	| isDynType t1 = do
		-- return constraints ? ~C t2
		return [Consistency DynType t2]

-- generate constraints and type for meet relation
meet :: Type -> Type -> (Type, Constraints)
meet t1 t2
	| isIntType t1 && isIntType t2 = (IntType, [])
	| isBoolType t1 && isBoolType t2 = (BoolType, [])
	| isParType t1 && isParType t2 && t1 == t2 = (t1, [])
	| isDynType t2 = (t1, [Consistency t1 DynType])
	| isDynType t1 = (t2, [Consistency DynType t2])
	| isVarType t1 = (t1, [Consistency t1 t2])
	| (not $ isVarType t1) && isVarType t2 = (t2, [Consistency t1 t2])
	| isArrowType t1 && isArrowType t2 =
		let
			(ArrowType t11 t12) = t1
			(ArrowType t21 t22) = t2
			(t1', constraints1) = meet t11 t21
			(t2', constraints2) = meet t12 t22
		in (ArrowType t1' t2', constraints1 ++ constraints2)

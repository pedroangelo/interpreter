module ConstraintGeneration (
	generateConstraints
) where

-- Syntax & Types
import Syntax
import Types

-- Imports
import Control.Monad.State
import Control.Monad.Except
import Data.Maybe

-- generate constraint set and type given a context and expression
generateConstraints :: (Context, Expression)
	-> StateT Int (Except String) (Type, Constraints)

-- (Cx) if expression is a variable
generateConstraints (ctx, Variable var) = do
	-- obtain type from context
	let varType = lookup var ctx
	-- check if variable exists in context
	if isNothing varType
		-- if not, throw error
		then throwError $ "Error: Variable " ++ var ++ " does not exist!! Terms must be closed!!"
		else do
			-- retrieve type
			let finalType = fromJust $ varType
			-- return type
			return (finalType, [])

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
	-- counter for variable creation
	i <- get
	put (i+1)
	-- create new type variable
	let newVar = newTypeVar i
	-- build for each expression in the application
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1) <- generateConstraints typeAssignment1
	(t2, constraints2) <- generateConstraints typeAssignment2
	-- return type along with all the constraints
	return (newVar, constraints1 ++ constraints2 ++ [Equality t1 (ArrowType t2 newVar)])

-- (C::) if expression is an ascription
generateConstraints (ctx, Ascription expr typ) = do
	-- build type assignment for expression
	let typeAssignment = (ctx, expr)
	-- obtain type and generate constraints for type assignment
	(exprType, constraints) <- generateConstraints typeAssignment
	-- return type along with all the constraints
	return (typ, constraints ++ [Equality exprType typ])

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
	return (newVar1, constraints ++ [Equality t1 (ArrowType newVar1 newVar2)])

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
	-- return type along with all the constraints
	return (t2, constraints1 ++ constraints2 ++ constraints3 ++ [Equality t1 BoolType, Equality t2 t3])

-- if expression is an arithmetic or relational operator
generateConstraints (ctx, expr)
	-- if expression is an addition (C+), subtraction (C-),
	-- multiplication (C*), or division (C/)
	| isArithmeticOperator expr = do
		-- build for each expression in the addition a type assignment
		let typeAssignment1 = (ctx, expr1)
		let typeAssignment2 = (ctx, expr2)
		-- obtain type and constraints for both expressions
		(t1, constraints1) <- generateConstraints typeAssignment1
		(t2, constraints2) <- generateConstraints typeAssignment2
		-- return type along with all the constraints
		return (IntType, constraints1 ++ constraints2 ++
			[Equality t1 IntType, Equality t2 IntType])
	-- if expression is an equality (C==), not equality (C/=), lesser than (C<),
	-- greater than (C>), lesser than or equal to (C<=) or greater than or equal to (C>=) check
	| isRelationalOperator expr = do
		-- build for each expression in the addition a type assignment
		let typeAssignment1 = (ctx, expr1)
		let typeAssignment2 = (ctx, expr2)
		-- obtain type and constraints for both expressions
		(t1, constraints1) <- generateConstraints typeAssignment1
		(t2, constraints2) <- generateConstraints typeAssignment2
		-- return type along with all the constraints
		return (BoolType, constraints1 ++ constraints2 ++
			[Equality t1 IntType, Equality t2 IntType])
	-- retrieve sub expressions from the operator
	where (expr1, expr2) = fromOperator expr

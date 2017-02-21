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
import Data.Char

-- generate constraint set and type given a context and expression
generateConstraints :: (Context, Expression) -> StateT Int (Except String) (Type, Constraints, Expression)

-- (Cx) if expression is a variable
generateConstraints (ctx, Variable var) = do
	-- obtain type from context
	let varType = lookup var ctx
	-- check if variable exists in context
	if isNothing varType
		-- if not, throw error
		then throwError $ "Variable " ++ var ++ " does not exist"
		else do
			-- retrieve type
			let finalType = fromJust $ varType
			i <- get
			-- replace quantified variables by type variables
			let (finalType', i') = runState (replaceQuantifiedVariables finalType) i
			put (i')
			-- build typed expression
			let typedExpr = TypeInformation finalType' (Variable var)
			-- return type
			return (finalType', [], typedExpr)

-- (Cλ) if expression is a abstraction
generateConstraints (ctx, Abstraction var expr) = do
	-- counter for variable creation
	i <- get
	put (i+1)
	-- create new type variable
	let newVar1 = newTypeVar i
	-- create a binding between the abstraction variable and the new type variable
	let binding = (var, ForAll "" newVar1)
	-- build type assignment with new binding
	let typeAssignment = (binding : ctx, expr)
	-- obtain type and generate constraints for new type assignment
	(exprType, constraints, expr_typed) <- generateConstraints typeAssignment
	-- build typed expression
	let typedExpr = TypeInformation (ArrowType newVar1 exprType) (Abstraction var expr_typed)
	-- return arrow type and constraints
	return (ArrowType newVar1 exprType, constraints, typedExpr)

-- (Capp) if expression is a application
generateConstraints (ctx, Application expr1 expr2) = do
	-- build for each expression in the application
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- get constraints for codomain and domain relation
	(t3, constraints3) <- codomain t1
	constraints4 <- domain t1 t2
	-- build typed expression
	let typedExpr = TypeInformation t3 (Application expr1_typed expr2_typed)
	-- return type along with all the constraints
	return (t3, constraints1 ++ constraints2 ++ constraints3 ++ constraints4, typedExpr)

-- (C::) if expression is an ascription
generateConstraints (ctx, Ascription expr typ) = do
	-- build type assignment for expression
	let typeAssignment = (ctx, expr)
	-- obtain type and generate constraints for type assignment
	(exprType, constraints, expr_typed) <- generateConstraints typeAssignment
	-- build typed expression
	let typedExpr = TypeInformation typ (Ascription expr_typed typ)
	-- return type along with all the constraints
	return (typ, constraints ++ [Consistency exprType typ], typedExpr)

-- (Cλ:) if expression is a annotated abstraction
generateConstraints (ctx, Annotation var typ expr) = do
	-- create a binding between the abstraction variable and the annotated type
	let binding = (var, ForAll "" typ)
	-- build type assignment with new binding
	let typeAssignment = (binding : ctx, expr)
	-- obtain type and generate constraints for new type assignment
	(exprType, constraints, expr_typed) <- generateConstraints typeAssignment
	-- build typed expression
	let typedExpr = TypeInformation (ArrowType typ exprType) (Annotation var typ expr_typed)
	-- return arrow type and constraints
	return (ArrowType typ exprType, constraints, typedExpr)

-- (Cn) if expression is a integer
generateConstraints (ctx, Int int) = do
	-- build typed expression
	let typedExpr = TypeInformation IntType (Int int)
	-- return Int type
	return (IntType, [], typedExpr)

-- (Cb) if expression is a boolean
generateConstraints (ctx, Bool bool) = do
	-- build typed expression
	let typedExpr = TypeInformation BoolType (Bool bool)
	-- return Bool type
	return (BoolType, [], typedExpr)

-- (Clet) if expression is a let binding
generateConstraints (ctx, Let var expr1 expr2) = do
	-- (Cletp) if expression is a let binding a value to a variable
	-- | isValue expr1 = do
		-- build type assignment for value
		let typeAssignment1 = (ctx, expr1)
		-- obtain type and generate constraints for type assignment
		(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
		-- generalize type variables
		let t1' = generalizeTypeVariables t1
		-- build type assignment for value
		let typeAssignment2 = ((var, t1') : ctx, expr2)
		-- obtain type and generate constraints for type assignment
		(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
		-- build typed expression
		let typedExpr = TypeInformation t2 (Let var expr1_typed expr2_typed)
		-- return type along with all the constraints
		return (t2, constraints1 ++ constraints2, typedExpr)
	-- (Clet) if expression is a let binding a expression to a variable
{-	| otherwise = do
		-- build type assignment for value
		let typeAssignment1 = (ctx, expr1)
		-- obtain type and generate constraints for type assignment
		(t1, _, expr1_typed) <- generateConstraints typeAssignment1
		-- generalize type variables
		let t1' = generalizeTypeVariables t1
		-- build type assignment for value
		let typeAssignment2 = ((var, t1') : ctx, expr2)
		-- obtain type and generate constraints for type assignment
		(_, _, expr2_typed) <- generateConstraints typeAssignment2
		-- build type assignment for expression
		let typeAssignment = (ctx, Application (Abstraction var expr2) (expr1))
		-- obtain type and generate constraints for type assignment
		(t, constraints, expr_typed) <- generateConstraints typeAssignment
		-- build typed expression
		let typedExpr = TypeInformation t (Let var expr1_typed expr2_typed)
		-- return type along with all the constraints
		return (t, constraints, typedExpr)
-}

-- (Cfix) if expression is a fixed point
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
	(t1, constraints, expr_typed) <- generateConstraints typeAssignment1
	-- build typed expression
	let typedExpr = TypeInformation newVar1 (Fix expr_typed)
	return (newVar1, constraints ++ [Consistency t1 (ArrowType newVar1 newVar2)], typedExpr)

-- (Cletrec) if expression is a recursive let binding
generateConstraints (ctx, LetRec var expr1 expr2) = do
	-- build type assignment
	let typeAssignment = (ctx, Let var (Fix $ Abstraction var expr1) expr2)
	-- obtain type and generate constraints for type assignment
	(t, constraints, _) <- generateConstraints typeAssignment
	-- build type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and generate constraints for type assignment
	(_, _, expr1_typed) <- generateConstraints typeAssignment
	(_, _, expr2_typed) <- generateConstraints typeAssignment
	-- build typed expression
	let typedExpr = TypeInformation t (LetRec var expr1_typed expr2_typed)
	return (t, constraints, typedExpr)

-- (Cif) if expression if a conditional statement
generateConstraints (ctx, If expr1 expr2 expr3) = do
	-- build for each expression in the application
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	let typeAssignment3 = (ctx, expr3)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	(t3, constraints3, expr3_typed) <- generateConstraints typeAssignment3
	let (t4, constraints4) = meet t2 t3
	-- build typed expression
	let typedExpr = TypeInformation t4 (If expr1_typed expr2_typed expr3_typed)
	-- return type along with all the constraints
	return (t4, constraints1 ++ constraints2
		++ constraints3 ++ constraints4 ++ [Consistency t1 BoolType], typedExpr)

-- (C+) if expression if an addition
generateConstraints (ctx, Addition expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- build typed expression
	let typedExpr = TypeInformation IntType (Addition expr1_typed expr2_typed)
	-- return type along with all the constraints
	return (IntType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType], typedExpr)

-- (C-) if expression if a subtraction
generateConstraints (ctx, Subtraction expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- build typed expression
	let typedExpr = TypeInformation IntType (Subtraction expr1_typed expr2_typed)
	-- return type along with all the constraints
	return (IntType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType], typedExpr)

-- (C*) if expression if a multiplication
generateConstraints (ctx, Multiplication expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- build typed expression
	let typedExpr = TypeInformation IntType (Multiplication expr1_typed expr2_typed)
	-- return type along with all the constraints
	return (IntType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType], typedExpr)

-- (C/) if expression if a division
generateConstraints (ctx, Division expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- build typed expression
	let typedExpr = TypeInformation IntType (Division expr1_typed expr2_typed)
	-- return type along with all the constraints
	return (IntType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType], typedExpr)

-- (C==) if expression if a equality check
generateConstraints (ctx, Equal expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- build typed expression
	let typedExpr = TypeInformation BoolType (Equal expr1_typed expr2_typed)
	-- return type along with all the constraints
	return (BoolType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType], typedExpr)

-- (C/=) if expression if a not equality check
generateConstraints (ctx, NotEqual expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- build typed expression
	let typedExpr = TypeInformation BoolType (NotEqual expr1_typed expr2_typed)
	-- return type along with all the constraints
	return (BoolType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType], typedExpr)

-- (C<) if expression if a lesser than check
generateConstraints (ctx, LesserThan expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- build typed expression
	let typedExpr = TypeInformation BoolType (LesserThan expr1_typed expr2_typed)
	-- return type along with all the constraints
	return (BoolType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType], typedExpr)

-- (C>) if expression if a greater than check
generateConstraints (ctx, GreaterThan expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- build typed expression
	let typedExpr = TypeInformation BoolType (GreaterThan expr1_typed expr2_typed)
	-- return type along with all the constraints
	return (BoolType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType], typedExpr)

-- (C<=) if expression if a lesser than or equal to check
generateConstraints (ctx, LesserEqualTo expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- build typed expression
	let typedExpr = TypeInformation BoolType (LesserEqualTo expr1_typed expr2_typed)
	-- return type along with all the constraints
	return (BoolType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType], typedExpr)

-- (C>=) if expression if a greater than or equal to
generateConstraints (ctx, GreaterEqualTo expr1 expr2) = do
	-- build for each expression in the addition
	-- a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- build typed expression
	let typedExpr = TypeInformation BoolType (GreaterEqualTo expr1_typed expr2_typed)
	-- return type along with all the constraints
	return (BoolType, constraints1 ++ constraints2 ++
		[Consistency t1 IntType, Consistency t2 IntType], typedExpr)

-- (C:) if expression if a type information
generateConstraints (ctx, e@(TypeInformation typ expr)) = do
	-- build type assignment
	let typeAssignment = (ctx, expr)
	-- obtain type and generate constraints for type assignment
	(t, constraints, _) <- generateConstraints typeAssignment
	-- return type along with all the constraints
	return (t, constraints, e)

-- Replace type parameters with type variables
replaceQuantifiedVariables :: Type -> State Int Type
replaceQuantifiedVariables (ForAll var typ) = do
	-- counter for variable creation
	i <- get
	put (i+1)
	-- obtain new type by replacing matched type parameters with fresh type variable
	let typ' = substituteType (ParType var, newTypeVar i) typ
	-- recursive call
	replaceQuantifiedVariables typ'
-- return when no more ForAll quantifier
replaceQuantifiedVariables e = return e

-- generate constraints and type for codomain relation
codomain :: Type -> StateT Int (Except String) (Type, Constraints)
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
	-- throw error
	| otherwise = throwError "codomain"

-- generate constraints for domain relation
domain :: Type -> Type -> StateT Int (Except String) Constraints
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
	-- throw error
	| otherwise = throwError "domain"

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

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
	-> StateT Int (Except String) (Type, Constraints, Expression)

-- (Cx) if expression is a variable
generateConstraints (ctx, Variable var) = do
	-- obtain type from context
	let varType = lookup var ctx
	-- check if variable exists in context
	if isNothing varType then
		-- if not, throw error
		throwError $ "Error: Variable " ++ var ++ " does not exist!! Terms must be closed!!"
	else do
		-- retrieve type
		let finalType = fromJust $ varType
		i <- get
		-- replace quantified variables by type variables
		-- instantiation of Damas-Milner
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
generateConstraints (ctx, Let var expr1 expr2)
	-- (Cletp) if expression is a let binding a value to a variable
	| isValue expr1 || isAnnotation expr1 = do
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
	| otherwise = do
		-- build type assignment for value
		--let typeAssignment1 = (ctx, expr1)
		-- obtain type and generate constraints for type assignment
		--(t1, _, expr1_typed) <- generateConstraints typeAssignment1
		-- generalize type variables
		--let t1' = generalizeTypeVariables t1
		-- build type assignment for value
		--let typeAssignment2 = ((var, t1') : ctx, expr2)
		-- obtain type and generate constraints for type assignment
		--(_, _, expr2_typed) <- generateConstraints typeAssignment2
		-- build type assignment for expression
		let typeAssignment = (ctx, Application (Abstraction var expr2) expr1)
		-- obtain type and generate constraints for type assignment
		(t, constraints, expr_typed) <- generateConstraints typeAssignment
		-- build typed expression
		--let typedExpr = TypeInformation t (Let var expr1_typed expr2_typed)
		-- return type along with all the constraints
		return (t, constraints, expr_typed)

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
	(t, constraints, expr_typed) <- generateConstraints typeAssignment
	-- build type assignment
	--let typeAssignment1 = (ctx, expr1)
	-- obtain type and generate constraints for type assignment
	--(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	-- generalize type variables
	--let t1' = generalizeTypeVariables t1
	-- build type assignment
	--let typeAssignment2 = ((var, t1') : ctx, expr2)
	-- obtain type and generate constraints for type assignment
	--(_, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- build typed expression
	--let typedExpr = TypeInformation t (LetRec var expr1_typed expr2_typed)
	return (t, constraints, expr_typed)

-- (Cif) if expression if a conditional statement
generateConstraints (ctx, If expr1 expr2 expr3) = do
	-- build for each expression in the application a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	let typeAssignment3 = (ctx, expr3)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	(t3, constraints3, expr3_typed) <- generateConstraints typeAssignment3
	(t4, constraints4) <- lift $ meet t2 t3
	-- build typed expression
	let typedExpr = TypeInformation t4 (If expr1_typed expr2_typed expr3_typed)
	-- return type along with all the constraints
	return (t4, constraints1 ++ constraints2
		++ constraints3 ++ constraints4 ++ [Consistency t1 BoolType], typedExpr)

-- if expression is an arithmetic or relational operator
generateConstraints (ctx, expr)
	-- if expression is an addition (C+), subtraction (C-),
	-- multiplication (C*), or division (C/)
	| isArithmeticOperator expr = do
		-- build for each expression in the addition a type assignment
		let typeAssignment1 = (ctx, expr1)
		let typeAssignment2 = (ctx, expr2)
		-- obtain type and constraints for both expressions
		(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
		(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
		-- build typed expression
		let expr_typed
		 	| isAddition expr = Addition expr1_typed expr2_typed
			| isSubtraction expr = Subtraction expr1_typed expr2_typed
			| isMultiplication expr = Multiplication expr1_typed expr2_typed
			| isDivision expr = Division expr1_typed expr2_typed
		-- insert type information
		let typedExpr = TypeInformation IntType expr_typed
		-- return type along with all the constraints
		return (IntType, constraints1 ++ constraints2 ++
			[Consistency t1 IntType, Consistency t2 IntType], typedExpr)
	-- if expression is an equality (C==), not equality (C/=), lesser than (C<),
	-- greater than (C>), lesser than or equal to (C<=) or greater than or equal to (C>=) check
	| isRelationalOperator expr = do
		-- build for each expression in the addition a type assignment
		let typeAssignment1 = (ctx, expr1)
		let typeAssignment2 = (ctx, expr2)
		-- obtain type and constraints for both expressions
		(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
		(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
		-- build typed expression
		let expr_typed
		 	| isEqual expr = Equal expr1_typed expr2_typed
			| isNotEqual expr = NotEqual expr1_typed expr2_typed
			| isLessThan expr = LesserThan expr1_typed expr2_typed
			| isGreaterThan expr = GreaterThan expr1_typed expr2_typed
			| isLessEqualTo expr = LesserEqualTo expr1_typed expr2_typed
			| isGreaterEqualTo expr = GreaterEqualTo expr1_typed expr2_typed
		-- insert type information
		let typedExpr = TypeInformation BoolType expr_typed
		-- return type along with all the constraints
		return (BoolType, constraints1 ++ constraints2 ++
			[Consistency t1 IntType, Consistency t2 IntType], typedExpr)
	-- retrieve sub expressions from the operator
	where (expr1, expr2) = fromOperator expr

-- (Cunit) if expression is an unit
generateConstraints (ctx, Unit) = do
	-- return type along with all the constraints
	return (UnitType, [], TypeInformation UnitType Unit)

-- (Cpair) if expression is a pair
generateConstraints (ctx, Pair expr1 expr2) = do
	-- build for each expression in the application a type assignment
	let typeAssignment1 = (ctx, expr1)
	let typeAssignment2 = (ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	-- build typed expression
	let typedExpr = TypeInformation (ProductType t1 t2) (Pair expr1_typed expr2_typed)
	-- return type along with all the constraints
	return (ProductType t1 t2, constraints1 ++ constraints2, typedExpr)

-- (Cfst) if expression is a first projection
generateConstraints (ctx, First expr) = do
	-- counter for variable creation
	i <- get
	put (i+2)
	-- create new type variable
	let newVar1 = newTypeVar i
	let newVar2 = newTypeVar (i+1)
	-- build type assignment
	let typeAssignment = (ctx, expr)
	-- obtain type and constraints for type assignment
	(t, constraints, expr_typed) <- generateConstraints typeAssignment
	-- build typed expression
	let typedExpr = TypeInformation newVar1 (First expr_typed)
	-- return type along with all the constraints
	return (newVar1, constraints ++ [Consistency t (ProductType newVar1 newVar2)], typedExpr)

-- (Csnd) if expression is a second projection
generateConstraints (ctx, Second expr) = do
	-- counter for variable creation
	i <- get
	put (i+2)
	-- create new type variable
	let newVar1 = newTypeVar i
	let newVar2 = newTypeVar (i+1)
	-- build type assignment
	let typeAssignment = (ctx, expr)
	-- obtain type and constraints for type assignment
	(t, constraints, expr_typed) <- generateConstraints typeAssignment
	-- build typed expression
	let typedExpr = TypeInformation newVar2 (Second expr_typed)
	-- return type along with all the constraints
	return (newVar2, constraints ++ [Consistency t (ProductType newVar1 newVar2)], typedExpr)

-- (Crecord) if expression is a record
generateConstraints (ctx, Record records) = do
	-- get labels and types
	let (labels, exprs) = fromRecords records
	-- build for each expression a type assignment
	let typeAssignments = map (\x -> (ctx, x)) exprs
	-- obtain type and constraints for both expressions
	results <- mapM generateConstraints typeAssignments
	-- get resulting types and constraints
	let (types, cs, exprs_typed) = unzip3 results
	-- build type
	let ts = zip labels types
	-- build typed expression
	let typedExpr = TypeInformation (RecordType ts) (Record $ zip labels exprs_typed)
	-- return type along with all the constraints
	return (RecordType ts, concat cs, typedExpr)

-- (Cprojection) if expression is a first projection
generateConstraints (ctx, Projection label expr typ) = do
	-- build type assignment
	let typeAssignment = (ctx, expr)
	-- obtain type and constraints for type assignment
	(t, constraints, expr_typed) <- generateConstraints typeAssignment
	-- if expression is annotated with a record type
	if isRecordType typ then do
		-- retrieve type
		let RecordType records = typ
		-- obtain type according to tag
		let tagType = lookup label records
		-- if type doesn't exist in record
		if isNothing tagType then do
			-- build typed expression
			let typedExpr = TypeInformation UnitType (Projection label expr_typed typ)
			let cs = [Equality typ (RecordType [(label, UnitType)])]
			return (UnitType, constraints ++ cs, typedExpr)
		else do
			-- get labels
			let (labels, _) = fromRecordType typ
			-- get constraints for each type in variant
			(types, constraints') <- recordComponents labels t
			-- create record type of type variables
			let list = zip labels types
			-- let type of expr be a type variable according to the label
			let finalType = fromJust $ lookup label list
			-- build typed expression
			let typedExpr = TypeInformation finalType (Projection label expr_typed typ)
			-- return type along with all the constraints
			return (finalType, constraints ++ constraints' ++
				[Consistency (RecordType list) typ], typedExpr)
	-- if expression is annotated with a wrong type
	else do
		-- build typed expression
		let typedExpr = TypeInformation UnitType (Projection label expr_typed typ)
		let typ' = RecordType [(label, UnitType)]
		return (UnitType, constraints ++ [Equality typ typ'], typedExpr)

-- (Ccase) if expression is a case
generateConstraints (ctx, Case expr (var1, expr1) (var2, expr2)) = do
	-- build type assignment
	let typeAssignment = (ctx, expr)
	-- obtain type and constraints for type assignment
	(t, constraints, expr_typed) <- generateConstraints typeAssignment
	-- get constraints for two sides of sum type
	((t1', t2'), constraints') <- sumComponents t
	-- build for each expression in the application a type assignment
	let typeAssignment1 = ((var1, t1') : ctx, expr1)
	let typeAssignment2 = ((var2, t2') : ctx, expr2)
	-- obtain type and constraints for both expressions
	(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
	(t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
	(t3, constraints3) <- lift $ meet t1 t2
	-- build typed expression
	let typedExpr = TypeInformation t3 (Case expr_typed (var1, expr1_typed) (var2, expr2_typed))
	-- return type along with all the constraints
	return (t3, constraints ++ constraints' ++
		constraints1 ++ constraints2 ++ constraints3, typedExpr)

-- (Cinl) if expression is a left tag
generateConstraints (ctx, LeftTag expr typ) = do
	-- counter for variable creation
	i <- get
	put (i+2)
	-- create new type variable
	let newVar1 = newTypeVar i
	let newVar2 = newTypeVar (i+1)
	-- build type assignment
	let typeAssignment = (ctx, expr)
	-- obtain type and constraints for type assignment
	(t, constraints, expr_typed) <- generateConstraints typeAssignment
	-- build typed expression
	let typedExpr = TypeInformation (SumType newVar1 newVar2) $ LeftTag expr_typed typ
	-- return type along with all the constraints
	return ((SumType newVar1 newVar2), constraints ++
		[Consistency typ (SumType newVar1 newVar2), Consistency t newVar1], typedExpr)

-- (Cinr) if expression is a right tag
generateConstraints (ctx, RightTag expr typ) = do
	-- counter for variable creation
	i <- get
	put (i+2)
	-- create new type variable
	let newVar1 = newTypeVar i
	let newVar2 = newTypeVar (i+1)
	-- build type assignment
	let typeAssignment = (ctx, expr)
	-- obtain type and constraints for type assignment
	(t, constraints, expr_typed) <- generateConstraints typeAssignment
	-- build typed expression
	let typedExpr = TypeInformation (SumType newVar1 newVar2) $ RightTag expr_typed typ
	-- return type along with all the constraints
	return ((SumType newVar1 newVar2), constraints ++
		[Consistency typ (SumType newVar1 newVar2), Consistency t newVar2], typedExpr)

-- (Ccasevariant) if expression is a variant case
generateConstraints (ctx, CaseVariant expr alternatives) = do
	-- build type assignment
	let typeAssignment = (ctx, expr)
	-- obtain type and constraints for type assignment
	(t, constraints, expr_typed) <- generateConstraints typeAssignment
	-- get constraints for each type in variant
	(types, constraints') <-
		variantComponents (fst3 $ fromAlternatives alternatives) t
	-- build for each expression a type assignment
	let typeAssignments = map
		(\x -> let
			-- get type variable from alternative
			var = snd3 $ snd x
			-- get expression from alternative
			expr' = trd3 $ snd x
			-- get type from types
			typ = fst x
			-- add to context variable with new type
			in ((var, typ) : ctx, expr'))
		$ zip types alternatives
	-- obtain type and constraints for expressions
	results <- mapM generateConstraints typeAssignments
	-- get resulting types, constraints and typed expressions
	let (ts, cs, exprs_typed) = unzip3 results
	(t3, constraints'') <- lift $ foldM meetM (head ts, []) (tail ts)
	-- build each typed expression
	let typedAlternatives = map
		(\x -> let
			-- get label
			label = fst3 $ fst x
			-- get var
			var = snd3 $ fst x
			-- get typed expression
			expr_typed = snd x
			in (label, var, expr_typed))
		$ zip alternatives exprs_typed
	-- build typed expression
	let typedExpr = TypeInformation t3 (CaseVariant expr_typed typedAlternatives)
	-- return type along with all the constraints
	return (t3, constraints ++ (concat cs) ++
		constraints' ++ constraints'', typedExpr)

-- (Ctag) if expression is a tag
generateConstraints (ctx, Tag label expr typ) = do
	-- build type assignment
	let typeAssignment = (ctx, expr)
	-- obtain type and constraints for type assignment
	(t, constraints, expr_typed) <- generateConstraints typeAssignment
	-- if expression is annotated with a variant type
	if isVariantType typ then do
		-- retrieve type
		let VariantType list = typ
		-- obtain type according to tag
		let tagType = lookup label list
		-- if type doesn't exist in variant
		if isNothing tagType then do
			-- build typed expression
			let typedExpr = TypeInformation typ (Tag label expr_typed typ)
			let cs = [Equality typ (VariantType [(label, t)])]
			return (typ, constraints ++ cs, typedExpr)
		else do
			-- number of alternatives
			let n = length list
			-- counter for variable creation
			i <- get
			put (i+n+1)
			-- create new type variables
			let typeVars = map newTypeVar [i..i+n]
			-- get labels
			let (labels, _) = fromVariantType typ
			-- create list
			let listVars = zip labels typeVars
			-- build typed expression
			let typedExpr = TypeInformation (VariantType listVars) (Tag label expr_typed typ)
			-- obtain type according to tag
			let tagTypeVar = fromJust $ lookup label listVars
			-- return type along with all the constraints
			return (VariantType listVars, constraints ++
				[Consistency (VariantType listVars) typ, Consistency tagTypeVar t], typedExpr)
	-- if expression is annotated with other than variant type
	else do
		let typ' = VariantType [(label, t)]
		-- build typed expression
		let typedExpr = TypeInformation typ' (Tag label expr_typed typ)
		return (typ', constraints ++ [Consistency typ typ'], typedExpr)

-- (Cfold) if expression is a fold
generateConstraints (ctx, Fold typ expr) = do
	-- counter for variable creation
	i <- get
	put (i+1)
	-- create new type variable
	let newVar1 = newTypeVar i
	-- build type assignment
	let typeAssignment = (ctx, expr)
	-- obtain type and constraints for type assignment
	(t, constraints, expr_typed) <- generateConstraints typeAssignment
	-- unfold type
	let (Mu var typ') = typ
	let t' = unfoldType (var, typ) typ'
	-- build typed expression
	let typedExpr = TypeInformation typ (Fold typ expr_typed)
	-- return type along with all the constraints
	return (typ, constraints ++	[Consistency t' t], typedExpr)

-- {-
-- (Cunfold) if expression is a unfold
generateConstraints (ctx, Unfold typ expr) = do
	-- counter for variable creation
	i <- get
	put (i+1)
	-- create new type variable
	let newVar1 = newTypeVar i
	-- build type assignment
	let typeAssignment = (ctx, expr)
	-- obtain type and constraints for type assignment
	(t, constraints, expr_typed) <- generateConstraints typeAssignment
	let (Mu var _) = typ
	(Mu var' typ', constraints2) <- muComponents var t
	-- unfold type
	let t' = unfoldType (var', Mu var' typ') typ'
	-- build typed expression
	let typedExpr = TypeInformation t' (Unfold typ expr_typed)
	-- return type along with all the constraints
	return (t', constraints ++ constraints2 ++
		[Consistency typ (Mu var' typ')], typedExpr)
-- -}

{-
-- (Cunfold) if expression is a unfold
generateConstraints (ctx, Unfold typ expr) = do
	-- counter for variable creation
	i <- get
	put (i+1)
	-- create new type variable
	let newVar1 = newTypeVar i
	-- build type assignment
	let typeAssignment = (ctx, expr)
	-- obtain type and constraints for type assignment
	(t, constraints, expr_typed) <- generateConstraints typeAssignment
	-- unfold type
	let (Mu var typ') = typ
	let t' = unfoldType (var, typ) typ'
	-- build typed expression
	let typedExpr = TypeInformation t' (Unfold typ expr_typed)
	-- return type along with all the constraints
	return (t', constraints ++ [Consistency typ t], typedExpr)
-}

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
	let typ' = substituteType (VarType var, newTypeVar i) typ
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
		-- return as type t2 and equality relation t = t1 -> t2
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
	| otherwise = throwError $ "Error: Type " ++ (show t) ++ " has no codomain!!"

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
	| otherwise = throwError $ "Error: Type " ++ (show t1) ++ " has no domain!!"

-- generate constraints and type for meet relation
meet :: Type -> Type -> Except String (Type, Constraints)
meet t1 t2
	| isIntType t1 && isIntType t2 = return (IntType, [])
	| isBoolType t1 && isBoolType t2 = return (BoolType, [])
	| isUnitType t1 && isUnitType t2 = return (UnitType, [])
	| isDynType t2 = return (t1, [Consistency t1 DynType])
	| isDynType t1 = return (t2, [Consistency DynType t2])
	| isVarType t1 = return (t1, [Consistency t1 t2])
	| (not $ isVarType t1) && isVarType t2 = return (t2, [Consistency t1 t2])
	| isArrowType t1 && isArrowType t2 = do
		let	(ArrowType t11 t12) = t1
		let (ArrowType t21 t22) = t2
		(t1', constraints1) <- meet t11 t21
		(t2', constraints2) <- meet t12 t22
		return (ArrowType t1' t2', constraints1 ++ constraints2)
	| isProductType t1 && isProductType t2 = do
		let	(ProductType t11 t12) = t1
		let (ProductType t21 t22) = t2
		(t1', constraints1) <- meet t11 t21
		(t2', constraints2) <- meet t12 t22
		return (ProductType t1' t2', constraints1 ++ constraints2)
	| isRecordType t1 && isRecordType t2 && compareLabels t1 t2 = do
		let (labels1, types1) = fromRecordType t1
		let (_, types2) = fromRecordType t2
		let list = zip types1 types2
		-- run meet for each pair of types
		results <- mapM (\x -> meet (fst x) (snd x)) list
		-- get resulting types
		let ts = map fst results
		-- get resulting constraints
		let cs = map snd results
		return (VariantType $ zip labels1 ts, concat cs)
	| isSumType t1 && isSumType t2 = do
		let	(SumType t11 t12) = t1
		let (SumType t21 t22) = t2
		(t1', constraints1) <- meet t11 t21
		(t2', constraints2) <- meet t12 t22
		return (SumType t1' t2', constraints1 ++ constraints2)
	| isVariantType t1 && isVariantType t2 && compareLabels t1 t2 = do
		let (labels1, types1) = fromVariantType t1
		let (_, types2) = fromVariantType t2
		let list = zip types1 types2
		-- run meet for each pair of types
		results <- mapM (\x -> meet (fst x) (snd x)) list
		-- get resulting types
		let ts = map fst results
		-- get resulting constraints
		let cs = map snd results
		return (VariantType $ zip labels1 ts, concat cs)
	| isMuType t1 && isMuType t2 && compareVars t1 t2 = do
		let (Mu var1 t1') = t1
		let (Mu var2 t2') = t2
		(t, constraints) <- meet t1' t2'
		return (Mu var1 t, constraints)
	| otherwise = throwError $
		"Error: Types " ++ (show t1) ++ " and " ++ (show t2) ++ " are not compatible!!"

meetM :: (Type, Constraints) -> Type -> Except String (Type, Constraints)
meetM (t1, c) t2 = do
	(t, constraints) <- meet t1 t2
	return (t, c ++ constraints)

-- get components of sum type
sumComponents :: Type -> StateT Int (Except String) ((Type, Type), Constraints)
sumComponents t
	-- if t is type variable
	| isVarType t = do
		-- create two new type variables t1 and t2
		i <- get
		put (i+2)
		let t1 = newTypeVar i
		let t2 = newTypeVar (i+1)
		-- return types and equality relation t = t1 + t2
		return ((t1, t2), [Equality t (SumType t1 t2)])
	-- if t is sum type
	| isSumType t = do
		-- let t1 and t2 such that t = t1 + t2
		let (SumType t1 t2) = t
		-- return types
		return ((t1,t2), [])
	-- if t is dynamic type
	| isDynType t = do
		-- return dynamic typ
		return ((DynType, DynType), [])
	-- throw error
	| otherwise =
		throwError $ "Error: Type " ++ (show t) ++ " is not a sum type!!"

-- get components of variant type
variantComponents :: [Label] -> Type
	-> StateT Int (Except String) ([Type], Constraints)
variantComponents labels t
	-- if t is type variable
	| isVarType t = do
		-- number of alternatives
		let n = length labels
		-- counter for variable creation
		i <- get
		put (i+n+1)
		-- create new type variables
		let typeVars = map newTypeVar [i..i+n]
		-- build type consisting of new type variables
		let list = zip labels typeVars
		-- return types and equality relation t = <li:Ti>
		return (typeVars, [Equality t (VariantType list)])
	-- if t is variant type
	| isVariantType t = do
		let (_, types) = fromVariantType t
		-- return types
		return (types, [])
	-- if t is dynamic type
	| isDynType t = do
		-- number of alternatives
		let n = length labels
		-- return dynamic type
		return (replicate n DynType, [])
	-- throw error
	| otherwise =
		throwError $ "Error: Type " ++ (show t) ++ " is not a variant type!!"

-- get components of variant type
recordComponents :: [Label] -> Type
	-> StateT Int (Except String) ([Type], Constraints)
recordComponents labels t
	-- if t is type variable
	| isVarType t = do
		-- number of alternatives
		let n = length labels
		-- counter for variable creation
		i <- get
		put (i+n+1)
		-- create new type variables
		let typeVars = map newTypeVar [i..i+n]
		-- build type consisting of new type variables
		let list = zip labels typeVars
		-- return types and equality relation t = <li:Ti>
		return (typeVars, [Equality t (RecordType list)])
	-- if t is variant type
	| isRecordType t = do
		let (_, types) = fromRecordType t
		-- return types
		return (types, [])
	-- if t is dynamic type
	| isDynType t = do
		-- number of alternatives
		let n = length labels
		-- return dynamic type
		return (replicate n DynType, [])
	-- throw error
	| otherwise =
		throwError $ "Error: Type " ++ (show t) ++ " is not a record type!!"

-- get components of recursive type
muComponents :: Var -> Type
	-> StateT Int (Except String) (Type, Constraints)
muComponents var t
	-- if t is type variable
	| isVarType t = do
		-- counter for variable creation
		i <- get
		put (i+1)
		-- create new type variable
		let typeVar = newTypeVar i
		-- build type consisting of new type variables
		let typ = Mu var typeVar
		-- return types and equality relation t = <li:Ti>
		return (typ, [Equality t typ])
	-- if t is variant type
	| isMuType t = do
		-- return type
		return (t, [])
	-- if t is dynamic type
	| isDynType t = do
		-- return dynamic type
		return (Mu var DynType, [])
	-- throw error
	| otherwise =
		throwError $ "Error: Type " ++ (show t) ++ " is not a recursive type!!"

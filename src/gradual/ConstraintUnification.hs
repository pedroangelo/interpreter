module ConstraintUnification (
	unifyConstraints
) where

-- Syntax & Types
import Syntax
import Types

-- Imports
import Control.Monad.Except
import Data.Maybe

-- unify constraints to generate substitutions
unifyConstraints :: [Type] -> Constraints -> Int -> Except String ([Type], TypeSubstitutions)
unifyConstraints types [] _ = do
	return (types, [])

-- for consistenty constraints
unifyConstraints types ((Consistency t1 t2) : cs) counter
	-- U ((t ~C t) : cs) => U cs
	| t1 == t2 = do
		unifyConstraints types cs counter
	-- U ((? ~C t) : cs) => U cs
	| t1 == DynType = do
		unifyConstraints (types ++ [t2]) cs counter
	-- U ((t ~C ?) : cs) => U cs
	| t2 == DynType = do
		unifyConstraints (types ++ [t1]) cs counter
	-- U ((t11 -> t12 ~C t21 -> t22) : cs)
	-- => U ((t12 ~C t22, t11 ~C t21) : cs)
	| isArrowType t1 && isArrowType t2 = do
		let (ArrowType t11 t12) = t1
		let (ArrowType t21 t22) = t2
		let constraints = [Consistency t12 t22, Consistency t11 t21]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t11 × t12 ~C t21 × t22) : cs)
	-- => U ((t12 ~C t22, t11 ~C t21) : cs)
	| isProductType t1 && isProductType t2 = do
		let (ProductType t11 t12) = t1
		let (ProductType t21 t22) = t2
		let constraints = [Consistency t12 t22, Consistency t11 t21]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t11 + t12 ~C t21 + t22) : cs)
	-- => U ((t12 ~C t22, t11 ~C t21) : cs)
	| isSumType t1 && isSumType t2 = do
		let (SumType t11 t12) = t1
		let (SumType t21 t22) = t2
		let constraints = [Consistency t12 t22, Consistency t11 t21]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t1 ~C t2) : cs), t1 ∉ TVars
	-- => U ((t2 ~C t1) : cs)
	| (not $ isVarType t1) && isVarType t2 = do
		let constraints = [Consistency t2 t1]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t1 ~C t2) : cs), t1 ∈ {Int, Bool} ∪ TVar ∪ TParam
	-- => U ((t1 =C t2) : cs)
	| isVarType t1 && (isIntType t2 || isBoolType t2 || isVarType t2) = do
		let constraints = [Equality t1 t2]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t1 ~C t21 -> t22) : cs), t1 ∉ Vars(t21 -> t22)
	-- => U ((t12 ~C t22, t11 ~C t21, t1 =C t11 -> t12) : cs)
	| isVarType t1 && isArrowType t2 && (not $ belongs t1 t2) = do
		let	t11 = newTypeVar counter
		let t12 = newTypeVar (counter + 1)
		let (ArrowType t21 t22) = t2
		let constraints = [Consistency t12 t22,
			Consistency t11 t21,
			Equality t1 (ArrowType t11 t12)]
		unifyConstraints types (constraints ++ cs) (counter+2)
	-- U ((t1 ~C t21 × t22) : cs), t1 ∉ Vars(t21 × t22)
	-- => U ((t12 ~C t22, t11 ~C t21, t1 =C t11 × t12) : cs)
	| isVarType t1 && isProductType t2 && (not $ belongs t1 t2) = do
		let	t11 = newTypeVar counter
		let t12 = newTypeVar (counter + 1)
		let (ProductType t21 t22) = t2
		let constraints = [Consistency t12 t22,
			Consistency t11 t21,
			Equality t1 (ProductType t11 t12)]
		unifyConstraints types (constraints ++ cs) (counter+2)
	-- U ((t1 ~C t21 + t22) : cs), t1 ∉ Vars(t21 + t22)
	-- => U ((t12 ~C t22, t11 ~C t21, t1 =C t11 + t12) : cs)
	| isVarType t1 && isSumType t2 && (not $ belongs t1 t2) = do
		let	t11 = newTypeVar counter
		let t12 = newTypeVar (counter + 1)
		let (SumType t21 t22) = t2
		let constraints = [Consistency t12 t22,
			Consistency t11 t21,
			Equality t1 (SumType t11 t12)]
		unifyConstraints types (constraints ++ cs) (counter+2)
	-- if no constraint matches, then throw error
	| otherwise = throwError $
		"Error: Types " ++ (show t1) ++ " and " ++ (show t2) ++ " are not consistent!!"

-- for equality constraints
unifyConstraints types ((Equality t1 t2) : cs) counter
	-- -- U ((t =C t) : cs) => U cs
	| t1 == t2 = do
		unifyConstraints types cs counter
	-- U ((t11 -> t12 =C t21 -> t22) : cs)
	-- => U ((t12 =C t22, t11 =C t21) : cs)
	| isArrowType t1 && isArrowType t2 = do
		let	(ArrowType t11 t12) = t1
		let (ArrowType t21 t22) = t2
		let constraints = [Equality t12 t22, Equality t11 t21]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t11 × t12 =C t21 × t22) : cs)
	-- => U ((t12 =C t22, t11 =C t21) : cs)
	| isProductType t1 && isProductType t2 = do
		let	(ProductType t11 t12) = t1
		let (ProductType t21 t22) = t2
		let constraints = [Equality t12 t22, Equality t11 t21]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t11 + t12 =C t21 + t22) : cs)
	-- => U ((t12 =C t22, t11 =C t21) : cs)
	| isSumType t1 && isSumType t2 = do
		let	(SumType t11 t12) = t1
		let (SumType t21 t22) = t2
		let constraints = [Equality t12 t22, Equality t11 t21]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t1 =C t2) : cs), t1 ∉ TVars
	-- => U ((t2 =C t1) : cs)
	| (not $ isVarType t1) && isVarType t2 = do
		let constraints = [Equality t2 t1]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t1 =C t2) : cs), t1 ∉ TVars
	-- => U ([t1 ↦ t2] cs) ∘ [t1 ↦ t2]
	| isVarType t1 && (not $ belongs t1 t2) = do
		let s = (t1, t2)
		(types', substitutions) <- unifyConstraints
			(map (substituteType s) types)
			(map (substituteConstraint s) cs) counter
		return $ (types', substitutions ++ [s])
	-- if no constraint matches, then throw error
	| otherwise = throwError $
		"Error: Types " ++ (show t1) ++ " and " ++ (show t2) ++ " are not equal!!"

-- test if type variable exists in typ
belongs :: Type -> Type -> Bool
belongs (VarType var) typ
	| isVarType typ =
		let (VarType var') = typ
		in var == var'
	| isArrowType typ =
		let (ArrowType t21 t22) = typ
		in (belongs (VarType var) t21) || (belongs (VarType var) t22)
	| isProductType typ =
		let (ProductType t21 t22) = typ
		in (belongs (VarType var) t21) || (belongs (VarType var) t22)
	| isSumType typ =
		let (SumType t21 t22) = typ
		in (belongs (VarType var) t21) || (belongs (VarType var) t22)
	| otherwise = False
belongs _ _ = False

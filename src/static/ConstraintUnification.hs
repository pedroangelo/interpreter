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
unifyConstraints :: Constraints -> Int -> Except String TypeSubstitutions
unifyConstraints [] _ = do
	return []
-- for equality constraints
unifyConstraints ((Equality t1 t2) : cs) counter
	-- -- U ((t =C t) : cs) => U cs
	| t1 == t2 = do
		unifyConstraints cs counter
	-- U ((t11 -> t12 =C t21 -> t22) : cs)
	-- => U ((t12 =C t22, t11 =C t21) : cs)
	| isArrowType t1 && isArrowType t2 = do
		let (ArrowType t11 t12) = t1
		let (ArrowType t21 t22) = t2
		let constraints = [Equality t12 t22, Equality t11 t21]
		unifyConstraints (constraints ++ cs) counter
	-- U ((t11 × t12 =C t21 × t22) : cs)
	-- => U ((t12 =C t22, t11 =C t21) : cs)
	| isProductType t1 && isProductType t2 = do
		let (ProductType t11 t12) = t1
		let (ProductType t21 t22) = t2
		let constraints = [Equality t12 t22, Equality t11 t21]
		unifyConstraints (constraints ++ cs) counter
	-- U ((t11 + t12 =C t21 + t22) : cs)
	-- => U ((t12 =C t22, t11 =C t21) : cs)
	| isSumType t1 && isSumType t2 = do
		let (SumType t11 t12) = t1
		let (SumType t21 t22) = t2
		let constraints = [Equality t12 t22, Equality t11 t21]
		unifyConstraints (constraints ++ cs) counter
	-- U ((<l1i:T1i> =C <l2i:T2i>) : cs)
	-- => U
	| isVariantType t1 && isVariantType t2 && compareLabels t1 t2 = do
		let (VariantType list1) = t1
		let (VariantType list2) = t2
		let constraints =
			map (\x -> Equality (snd $ fst x) (snd $ snd x)) $ zip list1 list2
		unifyConstraints (constraints ++ cs) counter
	-- U ((t1 =C t2) : cs), t1 ∉ TVars
	-- => U ((t2 =C t1) : cs)
	| (not $ isVarType t1) && isVarType t2 = do
		let constraints = [Equality t2 t1]
		unifyConstraints (constraints ++ cs) counter
	-- U ((t1 =C t2) : cs), t1 ∉ TVars
	-- => U ([t1 ↦ t2] cs) ∘ [t1 ↦ t2]
	| isVarType t1 && (not $ belongs t1 t2) = do
		let s = (t1, t2)
		substitutions <- (unifyConstraints (map (substituteConstraint s) cs) counter)
		return $ substitutions ++ [s]
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

-- compare labels of variant types
compareLabels :: Type -> Type -> Bool
compareLabels (VariantType list1) (VariantType list2) =
	and $ map (\x -> (fst $ fst x) == (fst $ snd x)) $ zip list1 list2
compareLabels _ _ = False

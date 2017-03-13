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
	-- U (({l1i:T1i} =C {l2i:T2i}) : cs)
	-- => U
	| isRecordType t1 && isRecordType t2 && compareLabels t1 t2 = do
		let (_, types1) = fromRecordType t1
		let (_, types2) = fromRecordType t2
		let constraints =
			map (\x -> Equality (fst x) (snd x)) $ zip types1 types2
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
		let (_, types1) = fromVariantType t1
		let (_, types2) = fromVariantType t2
		let constraints =
			map (\x -> Equality (fst x) (snd x)) $ zip types1 types2
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
	| isRecordType typ =
		let (_, types) = fromRecordType typ
		in any (belongs $ VarType var) types
	| otherwise = False
	| isSumType typ =
		let (SumType t21 t22) = typ
		in (belongs (VarType var) t21) || (belongs (VarType var) t22)
	| isVariantType typ =
		let (_, types) = fromVariantType typ
		in any (belongs $ VarType var) types
	| otherwise = False
belongs _ _ = False

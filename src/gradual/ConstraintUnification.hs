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
	-- => U ((t12 ~C t22) : (t11 ~C t21) : cs)
	| isArrowType t1 && isArrowType t2 = do
		let (ArrowType t11 t12) = t1
		let (ArrowType t21 t22) = t2
		let constraints = [Consistency t12 t22, Consistency t11 t21]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t11 × t12 ~C t21 × t22) : cs)
	-- => U ((t12 ~C t22) : (t11 ~C t21) : cs)
	| isProductType t1 && isProductType t2 = do
		let (ProductType t11 t12) = t1
		let (ProductType t21 t22) = t2
		let constraints = [Consistency t12 t22, Consistency t11 t21]
		unifyConstraints types (constraints ++ cs) counter
	-- U (({T1i} ~C {T2i}) : cs)
	-- => U ((T11 ~C T21) : ... : (T1n ~C T2n) : cs)
	| isTupleType t1 && isTupleType t2 && compareSize t1 t2 = do
		let TupleType types1 = t1
		let TupleType types2 = t2
		let constraints =
			map (\x -> Consistency (fst x) (snd x)) $ zip types1 types2
		unifyConstraints types (constraints ++ cs) counter
	-- U (({l1i:T1i} ~C {l2i:T2i}) : cs)
	-- => U ((T11 ~C T21) : ... : (T1n ~C T2n) : cs)
	| isRecordType t1 && isRecordType t2 && compareLabels t1 t2 = do
		let (_, types1) = fromRecordType t1
		let (_, types2) = fromRecordType t2
		let constraints =
			map (\x -> Consistency (fst x) (snd x)) $ zip types1 types2
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t11 + t12 ~C t21 + t22) : cs)
	-- => U ((t12 ~C t22) : (t11 ~C t21) : cs)
	| isSumType t1 && isSumType t2 = do
		let (SumType t11 t12) = t1
		let (SumType t21 t22) = t2
		let constraints = [Consistency t12 t22, Consistency t11 t21]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((<l1i:T1i> ~C <l2i:T2i>) : cs)
	-- => U ((T11 ~C T21) : ... : (T1n ~C T2n) : cs)
	| isVariantType t1 && isVariantType t2 && compareLabels t1 t2 = do
		let (_, types1) = fromVariantType t1
		let (_, types2) = fromVariantType t2
		let constraints =
			map (\x -> Consistency (fst x) (snd x)) $ zip types1 types2
		unifyConstraints types (constraints ++ cs) counter
	-- U ((μX.T1 ~C μX.T2) : cs)
	-- => U ((T1 ~C T2) : cs)
	| isMuType t1 && isMuType t2 && compareVars t1 t2 = do
		let Mu _ t1' = t1
		let Mu _ t2' = t2
		let constraints = [Consistency t1' t2']
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t1 ~C t2) : cs), t1 ∉ TVars
	-- => U ((t2 ~C t1) : cs)
	| (not $ isVarType t1) && isVarType t2 = do
		let constraints = [Consistency t2 t1]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t1 ~C t2) : cs), t2 ∈ {Int, Bool, Unit} ∪ TVar ∪ TParam
	-- => U ((t1 =C t2) : cs)
	| isVarType t1 && (isIntType t2 || isBoolType t2 || isUnitType t2 || isVarType t2) = do
		let constraints = [Equality t1 t2]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t1 ~C t21 -> t22) : cs), t1 ∉ Vars(t21 -> t22)
	-- => U ((t12 ~C t22) : (t11 ~C t21) : (t1 =C t11 -> t12) : cs)
	| isVarType t1 && isArrowType t2 && (not $ belongs t1 t2) = do
		let	t11 = newTypeVar counter
		let t12 = newTypeVar (counter + 1)
		let (ArrowType t21 t22) = t2
		let constraints = [Consistency t12 t22,
			Consistency t11 t21,
			Equality t1 (ArrowType t11 t12)]
		unifyConstraints types (constraints ++ cs) (counter+2)
	-- U ((t1 ~C t21 × t22) : cs), t1 ∉ Vars(t21 × t22)
	-- => U ((t12 ~C t22) : (t11 ~C t21) : (t1 =C t11 × t12) : cs)
	| isVarType t1 && isProductType t2 && (not $ belongs t1 t2) = do
		let	t11 = newTypeVar counter
		let t12 = newTypeVar (counter + 1)
		let (ProductType t21 t22) = t2
		let constraints = [Consistency t12 t22,
			Consistency t11 t21,
			Equality t1 (ProductType t11 t12)]
		unifyConstraints types (constraints ++ cs) (counter+2)
	-- U ((t1 ~C {ti}) : cs), t1 ∉ Vars({ti})
	-- => U ((t11 ~C t1) : ... : (t1n ~C tn) : (t1 =C {t1i}) : cs)
	| isVarType t1 && isTupleType t2 && (not $ belongs t1 t2) = do
		-- retrieve type
		let TupleType list = t2
		-- tuple size
		let n = length list
		-- create new type variables
		let typeVars = map newTypeVar [counter..counter+n-1]
		-- create constraints between new type variables and existing types
		let cs' = map
			(\x -> let
				-- get var
				var = fst x
				-- get type
				typ = snd x
				in (Consistency var typ))
			$ zip typeVars list
		let constraints = [Equality t1 $ TupleType typeVars]
		unifyConstraints types (cs' ++ constraints ++ cs) (counter+n)
	-- U ((t1 ~C {li:ti}) : cs), t1 ∉ Vars({li:ti})
	-- => U ((t11 ~C t1) : ... : (t1n ~C tn) : (t1 =C {l1i:t1i}) : cs)
	| isVarType t1 && isRecordType t2 && (not $ belongs t1 t2) = do
		-- retrieve type
		let RecordType list = t2
		-- number of alternatives
		let n = length list
		-- create new type variables
		let typeVars = map newTypeVar [counter..counter+n-1]
		-- get labels and types from variant type
		let (labels, types') = fromRecordType t2
		-- create constraints between new type variables and existing types
		let cs' = map
			(\x -> let
				-- get var
				var = fst x
				-- get type
				typ = snd x
				in (Consistency var typ))
			$ zip typeVars types'
		-- create variant type with type variables
		let recordVarType = zip labels typeVars
		let constraints = [Equality t1 $ RecordType recordVarType]
		unifyConstraints types (cs' ++ constraints ++ cs) (counter+n)
	-- U ((t1 ~C t21 + t22) : cs), t1 ∉ Vars(t21 + t22)
	-- => U ((t12 ~C t22) : (t11 ~C t21) : (t1 =C t11 + t12) : cs)
	| isVarType t1 && isSumType t2 && (not $ belongs t1 t2) = do
		let	t11 = newTypeVar counter
		let t12 = newTypeVar (counter + 1)
		let (SumType t21 t22) = t2
		let constraints = [Consistency t12 t22,
			Consistency t11 t21,
			Equality t1 (SumType t11 t12)]
		unifyConstraints types (constraints ++ cs) (counter+2)
	-- U ((t1 ~C <li:ti>) : cs), t1 ∉ Vars(<li:ti>)
	-- => U ((t11 ~C t1) : ... : (t1n ~C tn) : (t1 =C <l1i:t1i>) : cs)
	| isVarType t1 && isVariantType t2 && (not $ belongs t1 t2) = do
		-- retrieve type
		let VariantType list = t2
		-- number of alternatives
		let n = length list
		-- create new type variables
		let typeVars = map newTypeVar [counter..counter+n-1]
		-- get labels and types from variant type
		let (labels, types') = fromVariantType t2
		-- create constraints between new type variables and existing types
		let cs' = map
			(\x -> let
				-- get var
				var = fst x
				-- get type
				typ = snd x
				in (Consistency var typ))
			$ zip typeVars types'
		-- create variant type with type variables
		let variantVarType = zip labels typeVars
		let constraints = [Equality t1 $ VariantType variantVarType]
		unifyConstraints types (cs' ++ constraints ++ cs) (counter+n)
	-- U ((t1 ~C μX.t2) : cs), t1 ∉ Vars(μX.t2)
	-- => U ((t11 ~C t2) : (t1 =C μX.t11))
	| isVarType t1 && isMuType t2 && (not $ belongs t1 t2) = do
		let	t = newTypeVar counter
		let (Mu var t2') = t2
		let constraints = [Consistency t t2',
			Equality t1 (Mu var t)]
		unifyConstraints types (constraints ++ cs) (counter+2)
	-- if no constraint matches, then throw error
	| otherwise = throwError $
		"Error: Types " ++ (show t1) ++ " and " ++ (show t2) ++ " are not consistent!!"

-- for equality constraints
unifyConstraints types ((Equality t1 t2) : cs) counter
	-- U ((t =C t) : cs) => U cs
	| t1 == t2 = do
		unifyConstraints types cs counter
	-- U ((t11 -> t12 =C t21 -> t22) : cs)
	-- => U ((t12 =C t22) : (t11 =C t21) : cs)
	| isArrowType t1 && isArrowType t2 = do
		let	(ArrowType t11 t12) = t1
		let (ArrowType t21 t22) = t2
		let constraints = [Equality t12 t22, Equality t11 t21]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t11 × t12 =C t21 × t22) : cs)
	-- => U ((t12 =C t22) : (t11 =C t21) : cs)
	| isProductType t1 && isProductType t2 = do
		let	(ProductType t11 t12) = t1
		let (ProductType t21 t22) = t2
		let constraints = [Equality t12 t22, Equality t11 t21]
		unifyConstraints types (constraints ++ cs) counter
	-- U (({T1i} =C {T2i}) : cs)
	-- => U ((T11 =C T21) : ... : (T1n =C T2n) : cs)
	| isTupleType t1 && isTupleType t2 && compareSize t1 t2 = do
		let TupleType types1 = t1
		let TupleType types2 = t2
		let constraints =
			map (\x -> Equality (fst x) (snd x)) $ zip types1 types2
		unifyConstraints types (constraints ++ cs) counter
	-- U (({l1i:T1i} =C {l2i:T2i}) : cs)
	-- => U ((T11 =C T21) : ... : (T1n =C T2n) : cs)
	| isRecordType t1 && isRecordType t2 && compareLabels t1 t2 = do
		let (_, types1) = fromRecordType t1
		let (_, types2) = fromRecordType t2
		let constraints =
			map (\x -> Equality (fst x) (snd x)) $ zip types1 types2
		unifyConstraints types (constraints ++ cs) counter
	-- U ((t11 + t12 =C t21 + t22) : cs)
	-- => U ((t12 =C t22) :(t11 =C t21) : cs)
	| isSumType t1 && isSumType t2 = do
		let	(SumType t11 t12) = t1
		let (SumType t21 t22) = t2
		let constraints = [Equality t12 t22, Equality t11 t21]
		unifyConstraints types (constraints ++ cs) counter
	-- U ((<l1i:T1i> =C <l2i:T2i>) : cs)
	-- => U ((T11 =C T21) : ... : (T1n =C T2n) : cs)
	| isVariantType t1 && isVariantType t2 && compareLabels t1 t2 = do
		let (_, types1) = fromVariantType t1
		let (_, types2) = fromVariantType t2
		let constraints =
			map (\x -> Equality (fst x) (snd x)) $ zip types1 types2
		unifyConstraints types (constraints ++ cs) counter
	-- U ((μX.T1 =C μX.T2) : cs)
	-- => U ((T1 =C T2) : cs)
	| isMuType t1 && isMuType t2 && compareVars t1 t2 = do
		let (Mu var1 t1') = t1
		let (Mu var2 t2') = t2
		unifyConstraints types ([Equality t1' t2'] ++ cs) counter
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
	| isTupleType typ =
		let	TupleType types = typ
		in any (belongs $ VarType var) types
	| isRecordType typ =
		let	(_, types) = fromRecordType typ
		in any (belongs $ VarType var) types
	| isSumType typ =
		let (SumType t21 t22) = typ
		in (belongs (VarType var) t21) || (belongs (VarType var) t22)
	| isVariantType typ =
		let	(_, types) = fromVariantType typ
		in any (belongs $ VarType var) types
	| isMuType typ =
		let (Mu var' t') = typ
		in if var' == var
			then False
			else belongs (VarType var) t'
	| otherwise = False
belongs _ _ = False

module Types where

-- Imports
import Data.Char
import Data.List

-- Context holds bindings between variables and types
type Context = [Bindings]
type Bindings = (Var, Type)

-- Types in λ-calculus and extensions
data Type
	= VarType Var
	| ArrowType Type Type
	| IntType
	| BoolType
	| DynType
	| ForAll Var Type
	| UnitType
	| ProductType Type Type
	| RecordType [(Label, Type)]
	| SumType Type Type
	| VariantType [(Label, Type)]
	| Mu Var Type
	deriving (Show, Eq)

-- Constraints
type Constraints = [Constraint]
data Constraint
	= Equality Type Type
	| Consistency Type Type
	deriving (Show, Eq)

type Label = String
type Var = String

-- MAPPING

-- Type Mapping
mapType :: (Type -> Type) -> Type -> Type
mapType f t@(VarType var) = f t
mapType f t@(ArrowType t1 t2) = f (ArrowType (mapType f t1) (mapType f t2))
mapType f t@(IntType) = f t
mapType f t@(BoolType) = f t
mapType f t@(DynType) = f t
mapType f t@(ForAll var t') = f (ForAll var $ mapType f t')
mapType f t@(UnitType) = f t
mapType f t@(ProductType t1 t2) = f (ProductType (mapType f t1) (mapType f t2))
mapType f t@(RecordType ts) = f (RecordType $ map (\x -> (fst x, mapType f $ snd x)) ts)
mapType f t@(SumType t1 t2) = f (SumType (mapType f t1) (mapType f t2))
mapType f t@(VariantType ts) = f (VariantType $ map (\x -> (fst x, mapType f $ snd x)) ts)
mapType f t@(Mu var t') = f (Mu var $ mapType f t')

-- CHECKS

-- check if is variable type
isVarType :: Type -> Bool
isVarType (VarType _) = True
isVarType _ = False

-- check if is function type
isArrowType :: Type -> Bool
isArrowType (ArrowType _ _) = True
isArrowType _ = False

-- check if is integer type
isIntType :: Type -> Bool
isIntType (IntType) = True
isIntType _ = False

-- check if is boolean type
isBoolType :: Type -> Bool
isBoolType (BoolType) = True
isBoolType _ = False

-- check if is dynamic type
isDynType :: Type -> Bool
isDynType (DynType) = True
isDynType _ = False

-- check if is for all quantifier
isForAllType :: Type -> Bool
isForAllType (ForAll _ _) = True
isForAllType _ = False

-- check if is unit type
isUnitType :: Type -> Bool
isUnitType UnitType = True
isUnitType _ = False

-- check if is product type
isProductType :: Type -> Bool
isProductType (ProductType _ _) = True
isProductType _ = False

-- check if is record type
isRecordType :: Type -> Bool
isRecordType (RecordType _) = True
isRecordType _ = False

-- check if is sum type
isSumType :: Type -> Bool
isSumType (SumType _ _) = True
isSumType _ = False

-- check if is variant type
isVariantType :: Type -> Bool
isVariantType (VariantType _) = True
isVariantType _ = False

-- check if is recursive type
isMuType :: Type -> Bool
isMuType (Mu _ _) = True
isMuType _ = False

-- check if is ground type
isGroundType :: Type -> Bool
isGroundType (ArrowType DynType DynType) = True
isGroundType IntType = True
isGroundType BoolType = True
isGroundType (ForAll _ DynType) = True
isGroundType (UnitType) = True
isGroundType (ProductType DynType DynType) = True
isGroundType (RecordType ts) = all (\x -> isDynType $ snd x) ts
isGroundType (SumType DynType DynType) = True
isGroundType (VariantType ts) = all (\x -> isDynType $ snd x) ts
isGroundType (Mu _ DynType) = True
isGroundType _ = False

-- check if types have the same ground type
sameGround :: Type -> Type -> Bool
sameGround t1 t2 = getGroundType t1 == getGroundType t2

-- compare labels of variant types
compareLabels :: Type -> Type -> Bool
compareLabels t1@(RecordType list1) t2@(RecordType list2) =
	let
		(labels1, _) = fromRecordType t1
		(labels2, _) = fromRecordType t2
	in labels1 == labels2
compareLabels t1@(VariantType list1) t2@(VariantType list2) =
	let
		(labels1, _) = fromVariantType t1
		(labels2, _) = fromVariantType t2
	in labels1 == labels2
compareLabels _ _ = False

-- compare variables of forall and mu types
compareVars :: Type -> Type -> Bool
compareVars (Mu var1 _) (Mu var2 _) = var1 == var2

-- PROJECTIONS

-- get ground type
getGroundType :: Type -> Type
getGroundType (ArrowType _ _) = ArrowType DynType DynType
getGroundType IntType = IntType
getGroundType BoolType = BoolType
getGroundType (ForAll _ _) = ForAll "" DynType
getGroundType (UnitType) = UnitType
getGroundType (ProductType _ _) = ProductType DynType DynType
getGroundType (RecordType ts) = RecordType $ map (\x -> (fst x, DynType)) ts
getGroundType (SumType _ _) = SumType DynType DynType
getGroundType (VariantType ts) = VariantType $ map (\x -> (fst x, DynType)) ts
getGroundType (Mu var _) = Mu var DynType

-- get label and type from record type
fromRecordType :: Type -> ([Label], [Type])
fromRecordType (RecordType list) = unzip list

-- get label and type from variant type
fromVariantType :: Type -> ([Label], [Type])
fromVariantType (VariantType list) = unzip list

-- SUBSTITUTIONS
type TypeSubstitutions = [TypeSubstitution]
type TypeSubstitution = (Type, Type)

-- subsitute type
substituteType :: TypeSubstitution -> Type -> Type
substituteType s@(old, new) t@(VarType var)
	| old == t = new
	| otherwise = t
substituteType s@(old, new) t@(ArrowType t1 t2) =
	ArrowType (substituteType s t1) (substituteType s t2)
substituteType s@(old, new) t@(IntType) = t
substituteType s@(old, new) t@(BoolType) = t
substituteType s@(old, new) t@(DynType) = t
substituteType s@(old, new) t@(ForAll var t') =
	ForAll var $ substituteType s t'
substituteType s@(old, new) t@(UnitType) = t
substituteType s@(old, new) t@(ProductType t1 t2) =
	ProductType (substituteType s t1) (substituteType s t2)
substituteType s@(old, new) t@(RecordType ts) =
	RecordType $ map (\x -> (fst x, substituteType s $ snd x)) ts
substituteType s@(old, new) t@(SumType t1 t2) =
	SumType (substituteType s t1) (substituteType s t2)
substituteType s@(old, new) t@(VariantType ts) =
	VariantType $ map (\x -> (fst x, substituteType s $ snd x)) ts
substituteType s@(old, new) t@(Mu var typ)
	| isVarType old && isVarType new && var == oldVar =
		Mu newVar $ substituteType s typ
	| isVarType old && (not . isVarType) new && var == oldVar = t
	| otherwise = Mu var $ substituteType s typ
	where
		(VarType oldVar) = old
		(VarType newVar) = new

-- unfold type
unfoldType :: (String, Type) -> Type -> Type
unfoldType s@(old, new) t@(VarType var)
	| old == var = new
	| otherwise = t
unfoldType s@(old, new) t@(ArrowType t1 t2) =
	ArrowType (unfoldType s t1) (unfoldType s t2)
unfoldType s@(old, new) t@(IntType) = t
unfoldType s@(old, new) t@(BoolType) = t
unfoldType s@(old, new) t@(DynType) = t
unfoldType s@(old, new) t@(UnitType) = t
unfoldType s@(old, new) t@(ProductType t1 t2) =
	ProductType (unfoldType s t1) (unfoldType s t2)
unfoldType s@(old, new) t@(RecordType ts) =
	RecordType $ map (\x -> (fst x, unfoldType s $ snd x)) ts
unfoldType s@(old, new) t@(SumType t1 t2) =
	SumType (unfoldType s t1) (unfoldType s t2)
unfoldType s@(old, new) t@(VariantType ts) =
	VariantType $ map (\x -> (fst x, unfoldType s $ snd x)) ts
unfoldType s@(old, new) t@(Mu var typ)
	| old == var = unfoldType s typ
	| otherwise = t

-- apply substitution to constraints
substituteConstraint :: TypeSubstitution -> Constraint -> Constraint
substituteConstraint s (Equality t1 t2) =
	Equality (substituteType s t1) (substituteType s t2)
substituteConstraint s (Consistency t1 t2) =
	Consistency (substituteType s t1) (substituteType s t2)

-- HELPER FUNCTIONS

-- Bind type variables with ForAll quantifiers
generalizeTypeVariables :: Type -> Type
generalizeTypeVariables t =
	let
		-- get list of type variables
		(exclude, include) = countTypeVariable t
		vars = (nub include) \\ exclude
	-- insert forall quantifiers
	in buildForAll t vars

-- Collect type variables into a list
countTypeVariable :: Type -> ([String], [String])
countTypeVariable t@(VarType var) = ([] , [var])
countTypeVariable t@(ArrowType t1 t2) =
	let
		(exclude1, include1) = countTypeVariable t1
		(exclude2, include2) = countTypeVariable t2
	in (exclude1 ++ exclude2, include1 ++ include2)
countTypeVariable t@(ForAll var t') = countTypeVariable t'
countTypeVariable t@(ProductType t1 t2) =
	let
		(exclude1, include1) = countTypeVariable t1
		(exclude2, include2) = countTypeVariable t2
	in (exclude1 ++ exclude2, include1 ++ include2)
countTypeVariable t@(RecordType ts) =
	let
		result = map (countTypeVariable . snd) ts
		(exclude, include) = foldr1 (\x -> \y ->
			(nub $ fst x ++ fst y,
			nub $ snd x ++ snd y)) result
	in (exclude, include)
countTypeVariable t@(SumType t1 t2) =
	let
		(exclude1, include1) = countTypeVariable t1
		(exclude2, include2) = countTypeVariable t2
	in (exclude1 ++ exclude2, include1 ++ include2)
countTypeVariable t@(VariantType ts) =
	let
		result = map (countTypeVariable . snd) ts
		(exclude, include) = foldr1 (\x -> \y ->
			(nub $ fst x ++ fst y,
			nub $ snd x ++ snd y)) result
	in (exclude, include)
countTypeVariable t@(Mu var typ) =
	let (exclude, include) = countTypeVariable typ
	in (exclude ++ [var], include)
countTypeVariable t = ([], [])

-- Given a list of variable names, build forall quantifiers
buildForAll :: Type -> [String] -> Type
buildForAll t [] = t
buildForAll t vars =
	ForAll (head vars) $ buildForAll t $ tail vars

-- build new type variable
newTypeVar :: Int -> Type
newTypeVar index = VarType ("t" ++ show index)

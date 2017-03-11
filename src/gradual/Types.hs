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
	| SumType Type Type
	| VariantType [(Label, Type)]
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
mapType f t@(SumType t1 t2) = f (SumType (mapType f t1) (mapType f t2))
mapType f t@(VariantType ts) = f (VariantType $ map (\x -> (fst x, mapType f $ snd x)) ts)

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

-- check if is sum type
isSumType :: Type -> Bool
isSumType (SumType _ _) = True
isSumType _ = False

-- check if is variant type
isVariantType :: Type -> Bool
isVariantType (VariantType _) = True
isVariantType _ = False

-- check if is ground type
isGroundType :: Type -> Bool
isGroundType (ArrowType DynType DynType) = True
isGroundType IntType = True
isGroundType BoolType = True
isGroundType (ForAll _ DynType) = True
isGroundType (UnitType) = True
isGroundType (ProductType DynType DynType) = True
isGroundType (SumType DynType DynType) = True
isGroundType (VariantType ts) = all (\x -> isDynType $ snd x) ts
isGroundType _ = False

-- check if types have the same ground type
sameGround :: Type -> Type -> Bool
sameGround t1 t2 = getGroundType t1 == getGroundType t2

-- compare labels of variant types
compareLabels :: Type -> Type -> Bool
compareLabels t1@(VariantType list1) t2@(VariantType list2) =
	let
		(labels1, _) = fromVariant t1
		(labels2, _) = fromVariant t2
	in labels1 == labels2
compareLabels _ _ = False

-- PROJECTIONS

-- get ground type
getGroundType :: Type -> Type
getGroundType (ArrowType _ _) = ArrowType DynType DynType
getGroundType IntType = IntType
getGroundType BoolType = BoolType
getGroundType (ForAll _ _) = ForAll "" DynType
getGroundType (UnitType) = UnitType
getGroundType (ProductType _ _) = ProductType DynType DynType
getGroundType (SumType _ _) = SumType DynType DynType
getGroundType (VariantType ts) = VariantType $ map (\x -> (fst x, DynType)) ts

-- get label and type from variant type
fromVariant :: Type -> ([Label], [Type])
fromVariant (VariantType list) = unzip list

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
substituteType s@(old, new) t@(SumType t1 t2) =
	SumType (substituteType s t1) (substituteType s t2)
substituteType s@(old, new) t@(VariantType ts) =
	VariantType $ map (\x -> (fst x, substituteType s $ snd x)) ts

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
		vars = nub $ countTypeVariable t
	-- insert forall quantifiers
	in buildForAll t vars

-- Collect type variables into a list
countTypeVariable :: Type -> [String]
countTypeVariable t@(VarType var) = var : []
countTypeVariable t@(ArrowType t1 t2) = countTypeVariable t1 ++ countTypeVariable t2
countTypeVariable t@(ForAll var t') = countTypeVariable t'
countTypeVariable t@(ProductType t1 t2) = countTypeVariable t1 ++ countTypeVariable t2
countTypeVariable t@(SumType t1 t2) = countTypeVariable t1 ++ countTypeVariable t2
countTypeVariable t@(VariantType ts) = concat $ map (countTypeVariable . snd) ts
countTypeVariable t = []

-- Given a list of variable names, build forall quantifiers
buildForAll :: Type -> [String] -> Type
buildForAll t [] = t
buildForAll t vars =
	ForAll (head vars) $ buildForAll t $ tail vars

-- build new type variable
newTypeVar :: Int -> Type
newTypeVar index = VarType ("t" ++ show index)

-- given a test function, collect all types that suceed in the test
retrieveType :: (Type -> Bool) -> Type -> [Type]
retrieveType f t@(ArrowType t1 t2) =
	let
		t1' = retrieveType f t1
		t2' = retrieveType f t2
		t' = if f t then [t] else []
	in t' ++ t1' ++ t2'
retrieveType f t@(ForAll var typ) =
	let
		typ' = retrieveType f typ
		t' = if f t then [t] else []
	in t' ++ typ'
retrieveType f t@(ProductType t1 t2) =
	let
		t1' = retrieveType f t1
		t2' = retrieveType f t2
		t' = if f t then [t] else []
	in t' ++ t1' ++ t2'
retrieveType f t@(SumType t1 t2) =
	let
		t1' = retrieveType f t1
		t2' = retrieveType f t2
		t' = if f t then [t] else []
	in t' ++ t1' ++ t2'
retrieveType f t@(VariantType list) =
	let
		list' = map (\x -> retrieveType f (snd x)) list
		t' = if f t then [t] else []
	in t' ++ (concat list')
retrieveType f t = if f t then [t] else []

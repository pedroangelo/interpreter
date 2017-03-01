module Types where

-- Imports
import Data.Char
import Data.List

-- Context holds bindings between variables and types
type Context = [Bindings]
type Bindings = (String, Type)

-- Types in λ-calculus and extensions
-- Types
data Type
	= VarType String
	| ParType String
	| ArrowType Type Type
	| IntType
	| BoolType
	| ForAll String Type
	| UnitType
	| ProductType Type Type
	| SumType Type Type
	deriving (Show, Eq, Ord)

-- Constraints
type Constraints = [Constraint]
data Constraint
	= Equality Type Type
	deriving (Show, Eq)

-- Type Mapping
mapType :: (Type -> Type) -> Type -> Type
mapType f t@(VarType var) = f t
mapType f t@(ParType var) = f t
mapType f t@(ArrowType t1 t2) = f (ArrowType (mapType f t1) (mapType f t2))
mapType f t@(IntType) = f t
mapType f t@(BoolType) = f t
mapType f t@(ForAll var t') = f (ForAll var $ mapType f t')
mapType f t@(UnitType) = f t
mapType f t@(ProductType t1 t2) = f (ProductType (mapType f t1) (mapType f t2))
mapType f t@(SumType t1 t2) = f (SumType (mapType f t1) (mapType f t2))

-- HELPER FUNCTIONS

-- build new type variable
newTypeVar :: Int -> Type
newTypeVar index = VarType ("t" ++ show index)

-- build new type parameter
newTypePar :: Int -> Type
newTypePar index = ParType ("T" ++ show index)

-- check if is variable type
isVarType :: Type -> Bool
isVarType (VarType _) = True
isVarType _ = False

-- check if is parameter type
isParType :: Type -> Bool
isParType (ParType _) = True
isParType _ = False

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

-- SUBSTITUTIONS
type TypeSubstitutions = [TypeSubstitution]
type TypeSubstitution = (Type, Type)

-- subsitute type
substituteType :: TypeSubstitution -> Type -> Type
substituteType s@(old, new) t@(VarType var)
	| old == t = new
	| otherwise = t
substituteType s@(old, new) t@(ParType par)
	| old == t = new
	| otherwise = t
substituteType s@(old, new) t@(ArrowType t1 t2) =
	ArrowType (substituteType s t1) (substituteType s t2)
substituteType s@(old, new) t@(IntType) = t
substituteType s@(old, new) t@(BoolType) = t
substituteType s@(old, new) t@(UnitType) = t
substituteType s@(old, new) t@(ProductType t1 t2) =
	ProductType (substituteType s t1) (substituteType s t2)
substituteType s@(old, new) t@(SumType t1 t2) =
	SumType (substituteType s t1) (substituteType s t2)

-- apply substitution to constraints
substituteConstraint :: TypeSubstitution -> Constraint -> Constraint
substituteConstraint s (Equality t1 t2) =
	Equality (substituteType s t1) (substituteType s t2)

-- transform unconstrained type variables into type parameters
insertTypeParameters :: Type -> Type
insertTypeParameters = mapType insertTypeParameters'

-- transform unconstrained type variable into type parameter
insertTypeParameters' :: Type -> Type
insertTypeParameters' (VarType t) = ParType $ map toUpper t
insertTypeParameters' t = t

-- Bind type variables with ForAll quantifiers
generalizeTypeVariables :: Type -> Type
generalizeTypeVariables t =
	let
		-- get list of type variables
		vars = nub $ countTypeVariable t
		-- replace type variables with type parameters
		t' = insertTypeParameters t
	-- insert forall quantifiers
	in buildForAll t' vars

-- Collect type variables into a list
countTypeVariable :: Type -> [String]
countTypeVariable t@(VarType var) = var : []
countTypeVariable t@(ArrowType t1 t2) = countTypeVariable t1 ++ countTypeVariable t2
countTypeVariable t@(ForAll var t') = countTypeVariable t'
countTypeVariable t@(ProductType t1 t2) = countTypeVariable t1 ++ countTypeVariable t2
countTypeVariable t@(SumType t1 t2) = countTypeVariable t1 ++ countTypeVariable t2
countTypeVariable t = []

-- Given a list of variable names, build forall quantifiers
buildForAll :: Type -> [String] -> Type
buildForAll t [] = t
buildForAll t vars =
	ForAll (map toUpper $ head vars) $ buildForAll t $ tail vars

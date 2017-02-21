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
	| DynType
	| ForAll String Type
	deriving (Show, Eq, Ord)

-- Constraints
type Constraints = [Constraint]
data Constraint
	= Equality Type Type
	| Consistency Type Type
	deriving (Show, Eq)

-- Type Mapping
mapType :: (Type -> Type) -> Type -> Type
mapType f t@(VarType var) = f t
mapType f t@(ParType var) = f t
mapType f t@(ArrowType t1 t2) = f (ArrowType (mapType f t1) (mapType f t2))
mapType f t@(IntType) = f t
mapType f t@(BoolType) = f t
mapType f t@(DynType) = f t
mapType f t@(ForAll var t') = f (ForAll var $ mapType f t')

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

-- check if is dynamic type
isDynType :: Type -> Bool
isDynType (DynType) = True
isDynType _ = False

-- check if is for all quantifier
isForAllType :: Type -> Bool
isForAllType (ForAll _ _) = True
isForAllType _ = False

-- check if is ground type
isGroundType :: Type -> Bool
isGroundType (ArrowType DynType DynType) = True
isGroundType IntType = True
isGroundType BoolType = True
isGroundType (ForAll _ DynType) = True
isGroundType _ = False

getGroundType :: Type -> Type
getGroundType (ArrowType _ _) = ArrowType DynType DynType
getGroundType IntType = IntType
getGroundType BoolType = BoolType
getGroundType (ForAll _ _) = ForAll "" DynType

sameGround :: Type -> Type -> Bool
sameGround t1 t2 = getGroundType t1 == getGroundType t2

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
substituteType s@(old, new) t@(DynType) = t
substituteType s@(old, new) t@(ForAll var t') =
	ForAll var $ substituteType s t'

-- apply substitution to constraints
substituteConstraint :: TypeSubstitution -> Constraint -> Constraint
substituteConstraint s (Equality t1 t2) =
	Equality (instantiateTypeVariable s t1) (instantiateTypeVariable s t2)
substituteConstraint s (Consistency t1 t2) =
	Consistency (instantiateTypeVariable s t1) (instantiateTypeVariable s t2)

-- instantiate type variables with a type
instantiateTypeVariable :: TypeSubstitution -> Type -> Type
instantiateTypeVariable s = mapType (instantiateTypeVariable' s)

-- instantiate type variable with a type
instantiateTypeVariable' :: TypeSubstitution -> Type -> Type
instantiateTypeVariable' (s1, s2) t@(VarType var)
	| s1 == t = s2
	| otherwise = t
instantiateTypeVariable' s t = t

-- transform unconstrained type variables into type parameters
insertTypeParameters :: Type -> Type
insertTypeParameters = mapType insertTypeParameters'

-- transform unconstrained type variable into type parameter
insertTypeParameters' :: Type -> Type
insertTypeParameters' (VarType t) = ParType $ map toUpper t
insertTypeParameters' t = t

-- Bound type variables with ForAll quantifiers
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
countTypeVariable t = []

-- Given a list of variable names, build forall quantifiers
buildForAll :: Type -> [String] -> Type
buildForAll t [] = t
buildForAll t vars =
	ForAll (map toUpper $ head vars) $ buildForAll t $ tail vars

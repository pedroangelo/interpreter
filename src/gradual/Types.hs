module Types where

-- Imports
import Data.Char

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
	deriving (Show, Eq, Ord)

-- Constraints
type Constraints = [Constraint]
data Constraint
	= Equality Type Type
	| Consistency Type Type
	deriving (Show, Eq)

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

-- check if is ground type
isGroundType :: Type -> Bool
isGroundType (ArrowType DynType DynType) = True
isGroundType IntType = True
isGroundType BoolType = True
isGroundType _ = False

getGroundType :: Type -> Type
getGroundType (ArrowType _ _) = ArrowType DynType DynType
getGroundType IntType = IntType
getGroundType BoolType = BoolType

sameGround :: Type -> Type -> Bool
sameGround t1 t2 = getGroundType t1 == getGroundType t2

-- SUBSTITUTIONS
type TypeSubstitutions = [TypeSubstitution]
type TypeSubstitution = (Type, Type)

-- apply substitution to constraints
substituteConstraint :: TypeSubstitution -> Constraint -> Constraint
substituteConstraint s (Equality t1 t2) =
	Equality (instantiateTypeVariable s t1) (instantiateTypeVariable s t2)
substituteConstraint s (Consistency t1 t2) =
	Consistency (instantiateTypeVariable s t1) (instantiateTypeVariable s t2)

-- instantiate a type variable with a type
instantiateTypeVariable :: TypeSubstitution -> Type -> Type
instantiateTypeVariable (s1, s2) (VarType t)
	| s1 == (VarType t) = s2
	| otherwise = (VarType t)
instantiateTypeVariable (s1, s2) (ParType t) = ParType t
instantiateTypeVariable (s1, s2) (ArrowType t1 t2) =
	ArrowType (instantiateTypeVariable (s1, s2) t1) (instantiateTypeVariable (s1, s2) t2)
instantiateTypeVariable (s1, s2) IntType = IntType
instantiateTypeVariable (s1, s2) BoolType = BoolType
instantiateTypeVariable (s1, s2) DynType = DynType

-- transform unconstrained type variables into type parameters
insertTypeParameters :: Type -> Type
insertTypeParameters (VarType t) = ParType $ map toUpper t
insertTypeParameters (ParType t) = ParType t
insertTypeParameters (ArrowType t1 t2) = ArrowType (insertTypeParameters t1) (insertTypeParameters t2)
insertTypeParameters IntType = IntType
insertTypeParameters BoolType = BoolType
insertTypeParameters DynType = DynType

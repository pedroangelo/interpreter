module Types where

-- Imports
import Data.Char
import Data.List

-- Context holds bindings between variables and types
type Context = [Bindings]
type Bindings = (Var, (Type, Constraints))

-- Types in λ-calculus and extensions
data Type
	-- Type variable: Var
	= VarType Var
	-- Arrow type: Type -> Type
	| ArrowType Type Type
	-- Integer type: Int
	| IntType
	-- Boolean type: Bool
	| BoolType
	-- Dynamic type: Dyn
	| DynType
	-- For all quantifier: forall Var.Type
	| ForAll Var Type
	-- Unit type: Unit
	| UnitType
	-- Product type: Type × Type
	| ProductType Type Type
	-- Tuple type: (Types)
	| TupleType [Type]
	-- Record type: {Labels:Types}
	| RecordType [(Label, Type)]
	-- Sum type: Type + Type
	| SumType Type Type
	-- Variant type: <Labels:Types>
	| VariantType [(Label, Type)]
	-- List type: [Type]
	| ListType Type
	-- Recursive type: rec Var.Type
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
type Message = String

-- MAPPING

-- Type Mapping
mapType :: (Type -> Type) -> Type -> Type

-- Type variable
mapType f t@(VarType var) = f t

-- Arrow type
mapType f t@(ArrowType t1 t2) =
	f (ArrowType (mapType f t1) (mapType f t2))

-- Integer type
mapType f t@(IntType) = f t

-- Boolean type
mapType f t@(BoolType) = f t

-- Dynamic type
mapType f t@(DynType) = f t

-- For all quantifier
mapType f t@(ForAll var t') =
	f (ForAll var $ mapType f t')

-- Unit typ
mapType f t@(UnitType) = f t

-- Product type
mapType f t@(ProductType t1 t2) =
	f (ProductType (mapType f t1) (mapType f t2))

-- Tuple type
mapType f t@(TupleType ts) =
	f (TupleType $ map (mapType f) ts)

-- Record type
mapType f t@(RecordType ts) =
	f (RecordType $ map (\x -> (fst x, mapType f $ snd x)) ts)

-- Sum type
mapType f t@(SumType t1 t2) =
	f (SumType (mapType f t1) (mapType f t2))

-- Variant type
mapType f t@(VariantType ts) =
	f (VariantType $ map (\x -> (fst x, mapType f $ snd x)) ts)

-- List type
mapType f t@(ListType t') =
	f (ListType (mapType f t'))

-- Recursive type
mapType f t@(Mu var t') = f (Mu var $ mapType f t')

-- CHECKS

-- check if it's a variable type
isVarType :: Type -> Bool
isVarType (VarType _) = True
isVarType _ = False

-- check if it's a function type
isArrowType :: Type -> Bool
isArrowType (ArrowType _ _) = True
isArrowType _ = False

-- check if it's an integer type
isIntType :: Type -> Bool
isIntType (IntType) = True
isIntType _ = False

-- check if it's a boolean type
isBoolType :: Type -> Bool
isBoolType (BoolType) = True
isBoolType _ = False

-- check if it's a dynamic type
isDynType :: Type -> Bool
isDynType (DynType) = True
isDynType _ = False

-- check if it's a for all quantifier
isForAllType :: Type -> Bool
isForAllType (ForAll _ _) = True
isForAllType _ = False

-- check if it's an unit type
isUnitType :: Type -> Bool
isUnitType UnitType = True
isUnitType _ = False

-- check if it's a product type
isProductType :: Type -> Bool
isProductType (ProductType _ _) = True
isProductType _ = False

-- check if it's a tuple type
isTupleType :: Type -> Bool
isTupleType (TupleType _) = True
isTupleType _ = False

-- check if it's a record type
isRecordType :: Type -> Bool
isRecordType (RecordType _) = True
isRecordType _ = False

-- check if it's a sum type
isSumType :: Type -> Bool
isSumType (SumType _ _) = True
isSumType _ = False

-- check if it's a variant type
isVariantType :: Type -> Bool
isVariantType (VariantType _) = True
isVariantType _ = False

-- check if it's a list type
isListType :: Type -> Bool
isListType (ListType _) = True
isListType _ = False

-- check if it's a recursive type
isMuType :: Type -> Bool
isMuType (Mu _ _) = True
isMuType _ = False

-- check if it's a ground type
isGroundType :: Type -> Bool
isGroundType (ArrowType DynType DynType) = True
isGroundType IntType = True
isGroundType BoolType = True
isGroundType (ForAll _ DynType) = True
isGroundType (UnitType) = True
isGroundType (ProductType DynType DynType) = True
isGroundType (TupleType ts) = all isDynType ts
isGroundType (RecordType ts) = all (\x -> isDynType $ snd x) ts
isGroundType (SumType DynType DynType) = True
isGroundType (VariantType ts) = all (\x -> isDynType $ snd x) ts
isGroundType (ListType DynType) = True
isGroundType (Mu _ DynType) = True
isGroundType _ = False

-- check if types have the same ground type
sameGround :: Type -> Type -> Bool
sameGround t1 t2 = getGroundType t1 == getGroundType t2

-- compare labels of record and variant types
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

-- compare variables of mu type
compareVars :: Type -> Type -> Bool
compareVars (Mu var1 _) (Mu var2 _) = var1 == var2

-- compare size of tuple type
compareSize :: Type -> Type -> Bool
compareSize (TupleType ts1) (TupleType ts2) = length ts1 == length ts2

-- PROJECTIONS

-- get ground type
getGroundType :: Type -> Type
getGroundType (ArrowType _ _) = ArrowType DynType DynType
getGroundType IntType = IntType
getGroundType BoolType = BoolType
getGroundType (ForAll _ _) = ForAll "" DynType
getGroundType (UnitType) = UnitType
getGroundType (ProductType _ _) = ProductType DynType DynType
getGroundType (TupleType ts) = TupleType $ map (\x -> DynType) ts
getGroundType (RecordType ts) = RecordType $ map (\x -> (fst x, DynType)) ts
getGroundType (SumType _ _) = SumType DynType DynType
getGroundType (VariantType ts) = VariantType $ map (\x -> (fst x, DynType)) ts
getGroundType (ListType _) = ListType DynType
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

-- Type variable
substituteType s@(old, new) t@(VarType var)
	| old == t = new
	| otherwise = t

-- Arrow type
substituteType s@(old, new) t@(ArrowType t1 t2) =
	ArrowType (substituteType s t1) (substituteType s t2)

-- Integer type
substituteType s@(old, new) t@(IntType) = t

-- Boolean type
substituteType s@(old, new) t@(BoolType) = t

-- Dynamic type
substituteType s@(old, new) t@(DynType) = t

-- for all quantifier
substituteType s@(old, new) t@(ForAll var t') =
	ForAll var $ substituteType s t'

-- Unit type
substituteType s@(old, new) t@(UnitType) = t

-- Product type
substituteType s@(old, new) t@(ProductType t1 t2) =
	ProductType (substituteType s t1) (substituteType s t2)

-- Tuple type
substituteType s@(old, new) t@(TupleType ts) =
	TupleType $ map (substituteType s) ts

-- Record type
substituteType s@(old, new) t@(RecordType ts) =
	RecordType $ map (\x -> (fst x, substituteType s $ snd x)) ts

-- Sum type
substituteType s@(old, new) t@(SumType t1 t2) =
	SumType (substituteType s t1) (substituteType s t2)

-- Variant type
substituteType s@(old, new) t@(VariantType ts) =
	VariantType $ map (\x -> (fst x, substituteType s $ snd x)) ts

-- List type
substituteType s@(old, new) t@(ListType t') =
	ListType (substituteType s t')

-- Recursive type
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

-- Type variable
unfoldType s@(old, new) t@(VarType var)
	| old == var = new
	| otherwise = t

-- Arrow type
unfoldType s@(old, new) t@(ArrowType t1 t2) =
	ArrowType (unfoldType s t1) (unfoldType s t2)

-- Integer type
unfoldType s@(old, new) t@(IntType) = t

-- Boolean type
unfoldType s@(old, new) t@(BoolType) = t

-- Dynamic type
unfoldType s@(old, new) t@(DynType) = t

-- Unit type
unfoldType s@(old, new) t@(UnitType) = t

-- Product type
unfoldType s@(old, new) t@(ProductType t1 t2) =
	ProductType (unfoldType s t1) (unfoldType s t2)

-- Tuple type
unfoldType s@(old, new) t@(TupleType ts) =
	TupleType $ map (unfoldType s) ts

-- Record type
unfoldType s@(old, new) t@(RecordType ts) =
	RecordType $ map (\x -> (fst x, unfoldType s $ snd x)) ts

-- Sum type
unfoldType s@(old, new) t@(SumType t1 t2) =
	SumType (unfoldType s t1) (unfoldType s t2)

-- Variant type
unfoldType s@(old, new) t@(VariantType ts) =
	VariantType $ map (\x -> (fst x, unfoldType s $ snd x)) ts

-- List type
unfoldType s@(old, new) t@(ListType t') =
	ListType (unfoldType s t')

-- Recursive type
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
generalizeTypeVariables :: Context -> Type -> Type
generalizeTypeVariables ctx t =
	let
		freeVarsContext = nub $ concat $ map (\x -> freeVariables $ fst $ snd x) ctx
		freeVars = freeVariables t
	-- insert forall quantifiers
	in buildForAll t $ freeVars \\ freeVarsContext

freeVariables :: Type -> [String]
freeVariables t =
	let
		-- get list of type variables
		(exclude, include) = collectTypeVariables t
		-- remove type variables that are not free
		vars = (nub include) \\ exclude
	in vars

-- collect all type variables
collectTypeVariables :: Type -> ([String], [String])
collectTypeVariables t@(VarType var) = ([] , [var])
collectTypeVariables t@(ArrowType t1 t2) =
	let
		(exclude1, include1) = collectTypeVariables t1
		(exclude2, include2) = collectTypeVariables t2
	in (exclude1 ++ exclude2, include1 ++ include2)
collectTypeVariables t@(IntType) = ([],[])
collectTypeVariables t@(BoolType) = ([],[])
collectTypeVariables t@(DynType) = ([],[])
collectTypeVariables t@(ForAll var typ) =
	let (exclude, include) = collectTypeVariables typ
	in (exclude ++ [var], include)
collectTypeVariables t@(UnitType) = ([],[])
collectTypeVariables t@(ProductType t1 t2) =
	let
		(exclude1, include1) = collectTypeVariables t1
		(exclude2, include2) = collectTypeVariables t2
	in (exclude1 ++ exclude2, include1 ++ include2)
collectTypeVariables t@(TupleType ts) =
	let
		result = map collectTypeVariables ts
		(exclude, include) = foldr1 (\x -> \y ->
			(nub $ fst x ++ fst y,
			nub $ snd x ++ snd y)) result
	in (exclude, include)
collectTypeVariables t@(RecordType ts) =
	let
		result = map (collectTypeVariables . snd) ts
		(exclude, include) = foldr1 (\x -> \y ->
			(nub $ fst x ++ fst y,
			nub $ snd x ++ snd y)) result
	in (exclude, include)
collectTypeVariables t@(SumType t1 t2) =
	let
		(exclude1, include1) = collectTypeVariables t1
		(exclude2, include2) = collectTypeVariables t2
	in (exclude1 ++ exclude2, include1 ++ include2)
collectTypeVariables t@(VariantType ts) =
	let
		result = map (collectTypeVariables . snd) ts
		(exclude, include) = foldr1 (\x -> \y ->
			(nub $ fst x ++ fst y,
			nub $ snd x ++ snd y)) result
	in (exclude, include)
collectTypeVariables t@(ListType typ) = collectTypeVariables typ
collectTypeVariables t@(Mu var typ) =
	let (exclude, include) = collectTypeVariables typ
	in (exclude ++ [var], include)

-- Given a list of variable names, build forall quantifiers
buildForAll :: Type -> [String] -> Type
buildForAll t [] = t
buildForAll t vars =
	ForAll (head vars) $ buildForAll t $ tail vars

-- collect bound variables
collectBoundTypes :: Type -> [String]
collectBoundTypes (ForAll var typ) = var : collectBoundTypes typ
collectBoundTypes _ = []

-- remove for all quantifiers
removeQuantifiers :: Type -> Type
removeQuantifiers (ForAll _ typ) = removeQuantifiers typ
removeQuantifiers typ = typ

-- build new type variable
newTypeVar :: Int -> Type
newTypeVar index = VarType ("t" ++ show index)

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

snd3 :: (a, b, c) -> b
snd3 (_, b, _) = b

trd3 :: (a, b, c) -> c
trd3 (_, _, c) = c

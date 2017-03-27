module CastInsertion (
	insertCasts
) where

-- Syntax & Types
import Syntax
import Types

-- Imports
import Data.Maybe

-- insert casts in the expression
insertCasts :: Expression -> Expression

-- if expression is a value
insertCasts e@(TypeInformation _ (Variable _)) = e

-- if expression is an abstraction
insertCasts e@(TypeInformation typ (Abstraction var expr)) =
	TypeInformation typ $ Abstraction var $ insertCasts expr

-- if expression is an application
insertCasts e@(TypeInformation typ (Application expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- buid types
		TypeInformation t1 _ = expr1'
		TypeInformation t2 _ = expr2'
		d1 = patternMatchArrow t1
		ArrowType d2 t = d1
		-- build casts
		cast1 = Cast t1 d1 expr1'
		cast2 = Cast t2 d2 expr2'
	in TypeInformation typ $ Application cast1 cast2

-- if expression is an ascription
insertCasts e@(TypeInformation typ (Ascription expr typ')) =
	TypeInformation typ $ Ascription (insertCasts expr) typ'

-- if expression is an annotation
insertCasts e@(TypeInformation typ (Annotation var annotation expr)) =
	TypeInformation typ $ Annotation var annotation $ insertCasts expr

-- if expression is a integer
insertCasts e@(TypeInformation _ (Int _)) = e

-- if expression is a boolean
insertCasts e@(TypeInformation _ (Bool _)) = e

-- if expression is a let binding
insertCasts e@(TypeInformation typ (Let var expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
	in TypeInformation typ $ Let var expr1' expr2'

-- if expression is a fixed point operator
insertCasts e@(TypeInformation typ (Fix expr)) =
	let
		-- insert casts
		expr' = insertCasts expr
		-- build types
		TypeInformation t _ = expr'
		p = patternMatchArrow t
		ArrowType d _ = p
		-- build casts
		cast = Cast t (ArrowType d d) expr'
	in TypeInformation typ $ Fix cast

-- if expression is a recursive let binding
insertCasts e@(TypeInformation typ (LetRec var expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		TypeInformation t1 _ = expr1
		TypeInformation t1' _ = expr1'
		TypeInformation t2 _ = expr2'
		-- build casts
		cast = Cast t1' t1 expr1'
	in TypeInformation typ $ LetRec var cast expr2'

-- if expression is a conditional statement
insertCasts e@(TypeInformation typ (If expr1 expr2 expr3)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		expr3' = insertCasts expr3
		-- build types
		TypeInformation t1 _ = expr1'
		TypeInformation t2 _ = expr2'
		TypeInformation t3 _ = expr3'
		d = joinType t2 t3
		-- build casts
		cast1 = Cast t1 BoolType expr1'
		cast2 = Cast t2 d expr2'
		cast3 = Cast t3 d expr3'
	in TypeInformation typ $ If cast1 cast2 cast3

-- if expression is an arithmetic or relational operator
insertCasts e@(TypeInformation typ expr)
	-- if expression is an addition, subtraction, multiplication, or division
	| isArithmeticOperator expr =
		let
			-- insert casts
			expr1' = insertCasts expr1
			expr2' = insertCasts expr2
			-- build types
			TypeInformation t1 _ = expr1'
			TypeInformation t2 _ = expr2'
			-- build casts
			cast1 = Cast t1 IntType expr1'
			cast2 = Cast t2 IntType expr2'
			cast
				| isAddition expr = Addition cast1 cast2
				| isSubtraction expr = Subtraction cast1 cast2
				| isMultiplication expr = Multiplication cast1 cast2
				| isDivision expr = Division cast1 cast2
		in TypeInformation typ cast
	-- if expression is equality, not equality, lesser than,
	-- greater than, lesser than or equal to or greater than or equal to check
	| isRelationalOperator expr =
		let
			-- insert casts
			expr1' = insertCasts expr1
			expr2' = insertCasts expr2
			-- build types
			TypeInformation t1 _ = expr1'
			TypeInformation t2 _ = expr2'
			-- build casts
			cast1 = Cast t1 IntType expr1'
			cast2 = Cast t2 IntType expr2'
			cast
				| isEqual expr = Equal cast1 cast2
				| isNotEqual expr = NotEqual cast1 cast2
				| isLessThan expr = LesserThan cast1 cast2
				| isGreaterThan expr = GreaterThan cast1 cast2
				| isLessEqualTo expr = LesserEqualTo cast1 cast2
				| isGreaterEqualTo expr = GreaterEqualTo cast1 cast2
		in TypeInformation typ cast
	-- retrieve sub expressions from the operator
	where (expr1, expr2) = fromOperator expr

-- if expression is an unit
insertCasts e@(TypeInformation typ Unit) =
	TypeInformation typ Unit

-- if expression is a pair
insertCasts e@(TypeInformation typ (Pair expr1 expr2)) =
	let
		-- insert casts
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
	in TypeInformation typ $ Pair expr1' expr2'

-- if expression is a first projection
insertCasts e@(TypeInformation typ (First expr)) =
	let
		-- insert casts
		expr' = insertCasts expr
		-- buid types
		TypeInformation pm _ = expr'
		pm' = patternMatchProduct pm
		ProductType t1 t2 = pm'
		-- build casts
		cast = Cast pm pm' expr'
	in TypeInformation typ $ First cast

-- if expression is a second projection
insertCasts e@(TypeInformation typ (Second expr)) =
	let
		-- insert casts
		expr' = insertCasts expr
		-- buid types
		TypeInformation pm _ = expr'
		pm' = patternMatchProduct pm
		-- build casts
		cast = Cast pm pm' expr'
	in TypeInformation typ $ Second cast

-- if expression is a tuple
insertCasts e@(TypeInformation typ (Tuple exprs)) =
	TypeInformation typ $ Tuple $ map insertCasts exprs

-- if expression is a projection from tuple
insertCasts e@(TypeInformation typ (ProjectionTuple index expr typ')) =
	let
		-- insert casts
		expr' = insertCasts expr
		-- get labels
		TupleType types = typ'
		-- buid types
		TypeInformation pm _ = expr'
		TupleType pm' = patternMatchTuple pm (length types)
		-- build casts
		cast = Cast pm (TupleType pm') expr'
	in TypeInformation typ $ ProjectionTuple index cast typ'

-- if expression is a record
insertCasts e@(TypeInformation typ (Record records)) =
	let
		-- insert casts in records
		recordsCasts = map (\x -> (fst x, insertCasts $ snd x)) records
	in TypeInformation typ $ Record recordsCasts

-- if expression is a projection from record
insertCasts e@(TypeInformation typ (ProjectionRecord label expr typ')) =
	let
		-- insert casts
		expr' = insertCasts expr
		-- get labels
		(labels, _) = fromRecordType typ'
		-- buid types
		TypeInformation pm _ = expr'
		RecordType pm' = patternMatchRecords pm labels
		-- build casts
		cast = Cast pm (RecordType pm') expr'
	in TypeInformation typ $ ProjectionRecord label cast typ'

-- if expression is a case
insertCasts e@(TypeInformation typ (Case expr (var1, expr1) (var2, expr2))) =
	let
		-- insert casts
		expr' = insertCasts expr
		expr1' = insertCasts expr1
		expr2' = insertCasts expr2
		-- build types
		TypeInformation pm _ = expr'
		TypeInformation t1 _ = expr1'
		TypeInformation t2 _ = expr2'
		pm' = patternMatchSum pm
		j = joinType t1 t2
		-- build casts
		cast = Cast pm pm' expr'
		cast1 = Cast t1 j expr1'
		cast2 = Cast t2 j expr2'
	in TypeInformation typ $ Case cast (var1, cast1) (var2, cast2)

-- if expression is a left tag
insertCasts e@(TypeInformation typ (LeftTag expr t)) =
	TypeInformation typ $ LeftTag (insertCasts expr) t

-- if expression is a left tag
insertCasts e@(TypeInformation typ (RightTag expr t)) =
	TypeInformation typ $ RightTag (insertCasts expr) t

-- if expression is a variant case
insertCasts e@(TypeInformation typ (CaseVariant expr alternatives)) =
	let
		-- insert casts
		expr' = insertCasts expr
		-- insert casts in alternatives
		alternativesCasts = map (\x -> (fst3 x, snd3 x, insertCasts $ trd3 x)) alternatives
		-- build types
		TypeInformation pm _ = expr'
		-- get types for each alternative
		types = map (\x -> fromTypeInformation $ trd3 x) alternativesCasts
		-- get labels
		labels = fst3 $ fromAlternatives alternatives
		-- obtain pattern math of variant type
		VariantType pm' = patternMatchVariant pm labels
		-- get join type of all types from alternatives
		j = foldl joinType (head types) (tail types)
		-- build casts
		cast = Cast pm (VariantType pm') expr'
		casts = map
			(\x -> (fst3 $ snd x, snd3 $ snd x, Cast (fst x) j (trd3 $ snd x)))
			$ zip types alternativesCasts
	in TypeInformation typ $ CaseVariant cast casts

-- if expression is a tag
insertCasts e@(TypeInformation typ (Tag label expr t)) =
	TypeInformation typ $ Tag label (insertCasts expr) t

-- if expression is a fold
insertCasts e@(TypeInformation typ (Fold t expr)) =
	TypeInformation typ $ Fold t $ insertCasts expr

-- if expression is a unfold
insertCasts e@(TypeInformation typ (Unfold t expr)) =
	let
		-- insert casts
		expr' = insertCasts expr
		-- build types
		TypeInformation pm _ = expr'
		Mu var _ = t
		Mu var' typ' = patternMatchMu pm var
		finalType = unfoldType (var', Mu var' typ') typ'
		-- build casts
		cast = Cast pm (Mu var' typ') expr'
	in TypeInformation typ $ Unfold t cast

-- if expression is an error
insertCasts e@(TypeInformation _ (Error _)) = e

-- obtain pattern match type for arrow
patternMatchArrow :: Type -> Type
patternMatchArrow e@(ArrowType type1 type2) = e
patternMatchArrow e@(DynType) = ArrowType DynType DynType

-- obtain pattern match type for product
patternMatchProduct :: Type -> Type
patternMatchProduct e@(ProductType type1 type2) = e
patternMatchProduct e@(DynType) = ProductType DynType DynType

-- obtain pattern match type for tuples
patternMatchTuple :: Type -> Int -> Type
patternMatchTuple e@(TupleType _) i = e
patternMatchTuple e@(DynType) i =
	TupleType $ replicate i DynType

-- obtain pattern match type for records
patternMatchRecords :: Type -> [String] -> Type
patternMatchRecords e@(RecordType _) labels = e
patternMatchRecords e@(DynType) labels =
	RecordType $ map (\x -> (x, DynType)) labels

-- obtain pattern match type for sum
patternMatchSum :: Type -> Type
patternMatchSum e@(SumType type1 type2) = e
patternMatchSum e@(DynType) = SumType DynType DynType

-- obtain pattern match type for variant
patternMatchVariant :: Type -> [String] -> Type
patternMatchVariant e@(VariantType _) labels = e
patternMatchVariant e@(DynType) labels =
	VariantType $ map (\x -> (x, DynType)) labels

-- obtain pattern math type for recursive type
patternMatchMu :: Type -> Var -> Type
patternMatchMu e@(Mu var typ) _ = e
patternMatchMu e@(DynType) var = Mu var DynType

-- obtain join of types
joinType :: Type -> Type -> Type
joinType (ArrowType t11 t12) (ArrowType t21 t22) =
	let
		t1 = joinType t11 t21
		t2 = joinType t12 t22
	in ArrowType t1 t2
joinType (ProductType t11 t12) (ProductType t21 t22) =
	let
		t1 = joinType t11 t21
		t2 = joinType t12 t22
	in ProductType t1 t2
joinType (TupleType list1) (TupleType list2) =
	let
		list = map
			(\x -> let
				-- get types
				t1 = fst x
				t2 = snd x
				in (joinType t1 t2))
			$ zip list1 list2
	in TupleType list
joinType (RecordType list1) (RecordType list2) =
	let
		list = map
			(\x -> let
				-- get label
				label = fst $ fst x
				-- get types
				t1 = snd $ fst x
				t2 = snd $ snd x
				in (label, joinType t1 t2))
			$ zip list1 list2
	in RecordType list
joinType (SumType t11 t12) (SumType t21 t22) =
	let
		t1 = joinType t11 t21
		t2 = joinType t12 t22
	in SumType t1 t2
joinType (VariantType list1) (VariantType list2) =
	let
		list = map
			(\x -> let
				-- get label
				label = fst $ fst x
				-- get types
				t1 = snd $ fst x
				t2 = snd $ snd x
				in (label, joinType t1 t2))
			$ zip list1 list2
	in VariantType list
joinType (Mu var1 t1) (Mu var2 t2) =
	let
		t = joinType t1 t2
	in Mu var1 t
joinType t1 t2
	| (not (isArrowType t1) || not (isProductType t1) || not (isSumType t1) || not (isVariantType t1) || not (isRecordType t1) || not (isMuType t1)) &&
	 	(not (isArrowType t2) || not (isProductType t2) || not (isSumType t2) || not (isVariantType t2) || not (isRecordType t2) || not (isMuType t2)) =
		if (isDynType t1) then t2 else t1

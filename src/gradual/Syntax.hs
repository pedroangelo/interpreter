module Syntax where

-- Types
import Types

-- Expressions in λ-calculus and extensions
data Expression
	-- Pure λ-calculus terms
	= Variable Var
	| Abstraction Var Expression
	| Application Expression Expression
	-- Ascribed terms
	| Ascription Expression Type
	-- Annotated abstractions
	| Annotation Var Type Expression
	-- Integers
	| Int Int
	-- Booleans
	| Bool Bool
	-- Let bindings
	| Let Var Expression Expression
	-- Fixed point
	| Fix Expression
	-- Recursive let bindings
	| LetRec Var Expression Expression
	-- Conditional statements
	| If Expression Expression Expression
	-- Arithmetic operators
	| Addition Expression Expression
	| Subtraction Expression Expression
	| Multiplication Expression Expression
	| Division Expression Expression
	-- Relational operators
	| Equal Expression Expression
	| NotEqual Expression Expression
	| LesserThan Expression Expression
	| GreaterThan Expression Expression
	| LesserEqualTo Expression Expression
	| GreaterEqualTo Expression Expression
	-- Unit
	| Unit
	-- Pairs
	| Pair Expression Expression
	| First Expression
	| Second Expression
	-- Tuples
	| Tuple [Expression]
	| ProjectionTuple Int Expression Type
	-- Records
	| Record Records
	| ProjectionRecord Label Expression Type
	-- Sums
	| Case Expression (Var, Expression) (Var, Expression)
	| LeftTag Expression Type
	| RightTag Expression Type
	-- Variants
	| CaseVariant Expression Alternatives
	| Tag Label Expression Type
	-- Lists
	| Nil Type
	| Cons Type Expression Expression
	| IsNil Type Expression
	| Head Type Expression
	| Tail Type Expression
	-- Recursive types
	| Fold Type Expression
	| Unfold Type Expression
	-- Type annotations
	| TypeInformation Type Expression
	-- Casts
	| Cast Type Type Expression
	-- Blames
	| Blame Type Message
	-- Errors
	| Error Message
	deriving (Show, Eq)

type Alternatives = [Alternative]
type Alternative = (Label, Var, Expression)

type Records = [Record]
type Record = (Label, Expression)

-- MAPPING

-- Expression Mapping
mapExpression :: (Expression -> Expression) -> Expression -> Expression

-- Pure λ-calculus terms
mapExpression f e@(Variable var) = f e
mapExpression f e@(Abstraction var expr) =
	f (Abstraction var $ mapExpression f expr)
mapExpression f e@(Application expr1 expr2) =
	f (Application (mapExpression f expr1) (mapExpression f expr2))

-- Ascribed terms
mapExpression f e@(Ascription expr typ) =
	f (Ascription (mapExpression f expr) typ)

-- Annotated abstractions
mapExpression f e@(Annotation var typ expr) =
	f (Annotation var typ (mapExpression f expr))

-- Integers
mapExpression f e@(Int int) = f e

-- Booleans
mapExpression f e@(Bool bool) = f e

-- Let bindings
mapExpression f e@(Let var expr1 expr2) =
	f (Let var (mapExpression f expr1) (mapExpression f expr2))

-- Fixed point
mapExpression f e@(Fix expr) = f (Fix (mapExpression f expr))

-- Recursive let bindings
mapExpression f e@(LetRec var expr1 expr2) =
	f (LetRec var (mapExpression f expr1) (mapExpression f expr2))

-- Conditional statements
mapExpression f e@(If expr1 expr2 expr3) =
	f (If (mapExpression f expr1) (mapExpression f expr2) (mapExpression f expr3))

-- Arithmetic operators
mapExpression f e@(Addition expr1 expr2) =
	f (Addition (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(Subtraction expr1 expr2) =
	f (Subtraction (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(Multiplication expr1 expr2) =
	f (Multiplication (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(Division expr1 expr2) =
	f (Division (mapExpression f expr1) (mapExpression f expr2))

-- Relational operators
mapExpression f e@(Equal expr1 expr2) =
	f (Equal (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(NotEqual expr1 expr2) =
	f (NotEqual (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(LesserThan expr1 expr2) =
	f (LesserThan (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(GreaterThan expr1 expr2) =
	f (GreaterThan (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(LesserEqualTo expr1 expr2) =
	f (LesserEqualTo (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(GreaterEqualTo expr1 expr2) =
	f (GreaterEqualTo (mapExpression f expr1) (mapExpression f expr2))

-- Unit
mapExpression f e@(Unit) = f e

-- Pairs
mapExpression f e@(Pair expr1 expr2) =
	f (Pair (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(First expr) =
	f (First (mapExpression f expr))
mapExpression f e@(Second expr) =
	f (Second (mapExpression f expr))

-- Tuples
mapExpression f e@(Tuple exprs) =
	f (Tuple (map (mapExpression f) exprs))
mapExpression f e@(ProjectionTuple index expr typ) =
	f (ProjectionTuple index (mapExpression f expr) typ)

-- Records
mapExpression f e@(Record records) =
	f (Record (map (\x -> (fst x, mapExpression f (snd x))) records))
mapExpression f e@(ProjectionRecord label expr typ) =
	f (ProjectionRecord label (mapExpression f expr) typ)

-- Sums
mapExpression f e@(Case expr (var1, expr1) (var2, expr2)) =
	f (Case (mapExpression f expr) (var1, mapExpression f expr1) (var2, mapExpression f expr2))
mapExpression f e@(LeftTag expr typ) =
	f (LeftTag (mapExpression f expr) typ)
mapExpression f e@(RightTag expr typ) =
	f (RightTag (mapExpression f expr) typ)

-- Variants
mapExpression f e@(CaseVariant expr alternatives) =
	f (CaseVariant (mapExpression f expr) (map (\x -> (fst3 x, snd3 x, mapExpression f (trd3 x))) alternatives))
mapExpression f e@(Tag label expr typ) =
	f (Tag label (mapExpression f expr) typ)

-- Lists
mapExpression f e@(Nil typ) = f e
mapExpression f e@(Cons typ expr1 expr2) =
	f (Cons typ (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(IsNil typ expr) =
	f (IsNil typ (mapExpression f expr))
mapExpression f e@(Head typ expr) =
	f (Head typ (mapExpression f expr))
mapExpression f e@(Tail typ expr) =
	f (Tail typ (mapExpression f expr))

-- Recursive types
mapExpression f e@(Fold typ expr) =
	f (Fold typ (mapExpression f expr))
mapExpression f e@(Unfold typ expr) =
	f (Unfold typ (mapExpression f expr))

-- Type annotations
mapExpression f e@(TypeInformation typ expr) =
	f (TypeInformation typ (mapExpression f expr))

-- Casts
mapExpression f e@(Cast type1 type2 expr) =
	f (Cast type1 type2 (mapExpression f expr))

-- Blames
mapExpression f e@(Blame typ label) = f e

-- Errors
mapExpression f e@(Error msg) = f e

-- CHECKS

-- check if it's a variable
isVariable :: Expression -> Bool
isVariable (Variable _) = True
isVariable _ = False

-- check if it's an abstraction
isAbstraction :: Expression -> Bool
isAbstraction (Abstraction _ _) = True
isAbstraction _ = False

-- check if it's an application
isApplication :: Expression -> Bool
isApplication (Application _ _) = True
isApplication _ = False

-- check if it's an ascription
isAscription :: Expression -> Bool
isAscription (Ascription _ _) = True
isAscription _ = False

-- check if it's an annotated abstraction
isAnnotation :: Expression -> Bool
isAnnotation (Annotation _ _ _) = True
isAnnotation _ = False

-- check if it's a boolean
isBool :: Expression -> Bool
isBool (Bool _) = True
isBool _ = False

-- check if it's an integer
isInt :: Expression -> Bool
isInt (Int _) = True
isInt _ = False

-- check if it's a let binding
isLet :: Expression -> Bool
isLet (Let _ _ _) = True
isLet _ = False

-- check if it's a fixed point
isFix :: Expression -> Bool
isFix (Fix _) = True
isFix _ = False

-- check if it's a recursive let binding
isLetRec :: Expression -> Bool
isLetRec (LetRec _ _ _) = True
isLetRec _ = False

-- check if it's a conditional statement
isIf :: Expression -> Bool
isIf (If _ _ _) = True
isIf _ = False

-- check if it's an addition
isAddition :: Expression -> Bool
isAddition (Addition _ _) = True
isAddition _ = False

-- check if it's a subtraction
isSubtraction :: Expression -> Bool
isSubtraction (Subtraction _ _) = True
isSubtraction _ = False

-- check if it's a multiplication
isMultiplication :: Expression -> Bool
isMultiplication (Multiplication _ _) = True
isMultiplication _ = False

-- check if it's a division
isDivision :: Expression -> Bool
isDivision (Division _ _) = True
isDivision _ = False

-- check if it's an equality check
isEqual :: Expression -> Bool
isEqual (Equal _ _) = True
isEqual _ = False

-- check if it's a non equality check
isNotEqual :: Expression -> Bool
isNotEqual (NotEqual _ _) = True
isNotEqual _ = False

-- check if it's a lesser than check
isLessThan :: Expression -> Bool
isLessThan (LesserThan _ _) = True
isLessThan _ = False

-- check if it's a greater than check
isGreaterThan :: Expression -> Bool
isGreaterThan (GreaterThan _ _) = True
isGreaterThan _ = False

-- check if it's a lesser than or equal to check
isLessEqualTo :: Expression -> Bool
isLessEqualTo (LesserEqualTo _ _) = True
isLessEqualTo _ = False

-- check if it's a greater than or equal to check
isGreaterEqualTo :: Expression -> Bool
isGreaterEqualTo (GreaterEqualTo _ _) = True
isGreaterEqualTo _ = False

-- check if it's an unit
isUnit :: Expression -> Bool
isUnit Unit = True
isUnit _ = False

-- check if it's a pair
isPair :: Expression -> Bool
isPair (Pair _ _) = True
isPair _ = False

-- check if it's a first projection
isFirst :: Expression -> Bool
isFirst (First _) = True
isFirst _ = False

-- check if it's a second projection
isSecond :: Expression -> Bool
isSecond (Second _) = True
isSecond _ = False

-- check if it's a tuple
isTuple :: Expression -> Bool
isTuple (Tuple _) = True
isTuple _ = False

-- check if it's a projection from tuples
isProjectionTuple :: Expression -> Bool
isProjectionTuple (ProjectionTuple _ _ _) = True
isProjectionTuple _ = False

-- check if it's a record
isRecord :: Expression -> Bool
isRecord (Record _) = True
isRecord _ = False

-- check if it's a projection from records
isProjectionRecord :: Expression -> Bool
isProjectionRecord (ProjectionRecord _ _ _) = True
isProjectionRecord _ = False

-- check if it's a case
isCase :: Expression -> Bool
isCase (Case _ _ _) = True
isCase _ = False

-- check if it's a left tag
isLeftTag :: Expression -> Bool
isLeftTag (LeftTag _ _) = True
isLeftTag _ = False

-- check if it's a right tag
isRightTag :: Expression -> Bool
isRightTag (RightTag _ _) = True
isRightTag _ = False

-- check if it's a variant case
isCaseVariant :: Expression -> Bool
isCaseVariant (CaseVariant _ _) = True
isCaseVariant _ = False

-- check if it's a tag
isTag :: Expression -> Bool
isTag (Tag _ _ _) = True
isTag _ = False

-- check if is a empty list
isNil :: Expression -> Bool
isNil (Nil _) = True
isNil _ = False

-- check if is a list constructor
isCons :: Expression -> Bool
isCons (Cons _ _ _) = True
isCons _ = False

-- check if is a test for empty list
isIsNil :: Expression -> Bool
isIsNil (IsNil _ _) = True
isIsNil _ = False

-- check if is a head of a list
isHead :: Expression -> Bool
isHead (Head _ _) = True
isHead _ = False

-- check if is a tail of a list
isTail :: Expression -> Bool
isTail (Tail _ _) = True
isTail _ = False

-- check if it's a fold
isFold :: Expression -> Bool
isFold (Fold _ _) = True
isFold _ = False

-- check if it's an unfold
isUnfold :: Expression -> Bool
isUnfold (Unfold _ _) = True
isUnfold _ = False

-- check if it's a type information
isTypeInformation :: Expression -> Bool
isTypeInformation (TypeInformation _ _) = True
isTypeInformation _ = False

-- check if it's a cast
isCast :: Expression -> Bool
isCast (Cast _ _ _) = True
isCast _ = False

-- check if it's a blame
isBlame :: Expression -> Bool
isBlame (Blame _ _) = True
isBlame _ = False

-- check if it's an error
isError :: Expression -> Bool
isError (Error _) = True
isError _ = False

-- check if it's a value
isValue :: Expression -> Bool
isValue e =
	isVariable e ||
	isAbstraction e ||
	isBool e ||
	isInt e ||
	isUnit e ||
	(isPair e && isValuePair e) ||
	(isTuple e && isValueTuple e) ||
	(isRecord e && isValueRecord e) ||
	((isLeftTag e || isRightTag e) && isValueSums e) ||
	(isTag e && isValueVariants e) ||
	(isNil e) ||
	(isCons e && isValueCons e) ||
	isFold e ||
	isValueCast e ||
	isBlame e ||
	isError e

-- check if pair is a value
isValuePair :: Expression -> Bool
isValuePair (Pair expr1 expr2) = isValue expr1 && isValue expr2
isValuePair _ = False

-- check if tuple is a value
isValueTuple :: Expression -> Bool
isValueTuple (Tuple exprs) = all isValue exprs
isValueTuple _ = False

-- check if record is a value
isValueRecord :: Expression -> Bool
isValueRecord (Record records) = all (\x -> isValue $ snd x) records
isValueRecord _ = False

-- check if sum is a value
isValueSums :: Expression -> Bool
isValueSums (LeftTag expr _) = isValue expr
isValueSums (RightTag expr _) = isValue expr
isValueSums _ = False

-- check if variant tag is a value
isValueVariants :: Expression -> Bool
isValueVariants (Tag _ expr _) = isValue expr
isValueVariants _ = False

-- check if list constructor is a value
isValueCons :: Expression -> Bool
isValueCons (Cons _ expr1 expr2) = isValue expr1 && isValue expr2
isValueCons _ = False

-- check if cast is a value
isValueCast :: Expression -> Bool
isValueCast (Cast t1 t2 e) =
	(isGroundType t1 && isDynType t2 && isValue e) ||
	(isArrowType t1 && isArrowType t2 && isValue e && t1 /= t2) ||
	(isProductType t1 && isProductType t2 && isValue e && t1 /= t2) ||
	(isTupleType t1 && isTupleType t2 && isValue e && t1 /= t2) ||
	(isRecordType t1 && isRecordType t2 && isValue e && t1 /= t2) ||
	(isSumType t1 && isSumType t2 && isValue e && t1 /= t2) ||
	(isVariantType t1 && isVariantType t2 && isValue e && t1 /= t2) ||
	(isListType t1 && isListType t2 && isValue e && t1 /= t2) ||
	(isForAllType t1 && isForAllType t2 && isValue e && t1 /= t2) ||
	(isMuType t1 && isMuType t2 && isValue e && t1 /= t2)
isValueCast _ = False

-- check if it's an arithmetic operator
isArithmeticOperator :: Expression -> Bool
isArithmeticOperator (Addition _ _) = True
isArithmeticOperator (Subtraction _ _) = True
isArithmeticOperator (Multiplication _ _) = True
isArithmeticOperator (Division _ _) = True
isArithmeticOperator _ = False

-- check if it's a relational operator
isRelationalOperator :: Expression -> Bool
isRelationalOperator (Equal _ _) = True
isRelationalOperator (NotEqual _ _) = True
isRelationalOperator (LesserThan _ _) = True
isRelationalOperator (GreaterThan _ _) = True
isRelationalOperator (LesserEqualTo _ _) = True
isRelationalOperator (GreaterEqualTo _ _) = True
isRelationalOperator _ = False

-- PROJECTIONS

-- get expressions from arithmetic and relational operators
fromOperator :: Expression -> (Expression, Expression)
fromOperator (Addition expr1 expr2) = (expr1, expr2)
fromOperator (Subtraction expr1 expr2) = (expr1, expr2)
fromOperator (Multiplication expr1 expr2) = (expr1, expr2)
fromOperator (Division expr1 expr2) = (expr1, expr2)
fromOperator (Equal expr1 expr2) = (expr1, expr2)
fromOperator (NotEqual expr1 expr2) = (expr1, expr2)
fromOperator (LesserThan expr1 expr2) = (expr1, expr2)
fromOperator (GreaterThan expr1 expr2) = (expr1, expr2)
fromOperator (LesserEqualTo expr1 expr2) = (expr1, expr2)
fromOperator (GreaterEqualTo expr1 expr2) = (expr1, expr2)

-- get type from type information
fromTypeInformation :: Expression -> Type
fromTypeInformation (TypeInformation typ _) = typ

-- get label, var and expr from alternatives
fromAlternatives :: Alternatives -> ([Label], [Var], [Expression])
fromAlternatives = unzip3

fromRecords :: Records -> ([Label], [Expression])
fromRecords = unzip

-- SUBSTITUTIONS
type ExpressionSubstitution = (String, Expression)

-- Substitute expressions according to substitution
substitute :: ExpressionSubstitution -> Expression -> Expression

-- Pure λ-calculus terms
substitute s@(old, new) e@(Variable var)
	-- if var equals old, replace variable with new expression
	| var == old = new
	-- otherwise, do nothing
	| otherwise = e
substitute s@(old, new) e@(Abstraction var expr)
	-- if some abstraction has already binded the variable, don't propagate substitutions
	| var == old = e
	-- otherwise, propagate substitutions
	| otherwise = Abstraction var $ substitute s expr
substitute s@(old, new) e@(Application expr1 expr2) =
	Application (substitute s expr1) (substitute s expr2)

-- Ascribed terms
substitute s@(old, new) e@(Ascription expr typ) =
	Ascription (substitute s expr) typ

-- Annotated abstractions
substitute s@(old, new) e@(Annotation var typ expr)
	-- if some abstraction has already binded the variable, don't propagate substitutions
	| var == old = e
	-- otherwise, propagate substitutions
	| otherwise = Annotation var typ $ substitute s expr

-- Integers
substitute s@(old, new) e@(Bool _) = e

-- Booleans
substitute s@(old, new) e@(Int _) = e

-- Let bindings
substitute s@(old, new) e@(Let var expr1 expr2)
	-- if let has already binded the variable, dont propagate substitutions
	| var == old = e
	-- otherwise, propagate substitutions
	| otherwise = Let var (substitute s expr1) (substitute s expr2)

-- Fixed point
substitute s@(old, new) e@(Fix expr) = Fix $ substitute s expr

-- Recursive let bindings
substitute s@(old, new) e@(LetRec var expr1 expr2)
	-- if let has already binded the variable, dont propagate substitutions
	| var == old = e
	-- otherwise, propagate substitutions
	| otherwise = LetRec var (substitute s expr1) (substitute s expr2)

-- Conditional statements
substitute s@(old, new) e@(If expr1 expr2 expr3) =
	If (substitute s expr1) (substitute s expr2) (substitute s expr3)

-- Arithmetic operators
substitute s@(old, new) e@(Addition expr1 expr2) =
	Addition (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(Subtraction expr1 expr2) =
	Subtraction (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(Multiplication expr1 expr2) =
	Multiplication (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(Division expr1 expr2) =
	Division (substitute s expr1) (substitute s expr2)

-- Relational operators
substitute s@(old, new) e@(Equal expr1 expr2) =
	Equal (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(NotEqual expr1 expr2) =
	NotEqual (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(LesserThan expr1 expr2) =
	LesserThan (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(GreaterThan expr1 expr2) =
	GreaterThan (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(LesserEqualTo expr1 expr2) =
	LesserEqualTo (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(GreaterEqualTo expr1 expr2) =
	GreaterEqualTo (substitute s expr1) (substitute s expr2)

-- Unit
substitute s@(old, new) e@(Unit) = e

-- Pairs
substitute s@(old, new) e@(Pair expr1 expr2) =
	Pair (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(First expr) =
	First (substitute s expr)
substitute s@(old, new) e@(Second expr) =
	Second (substitute s expr)

-- Tuples
substitute s@(old, new) e@(Tuple exprs) =
	Tuple (map (substitute s) exprs)
substitute s@(old, new) e@(ProjectionTuple index expr typ) =
	ProjectionTuple index (substitute s expr) typ

-- Records
substitute s@(old, new) e@(Record records) =
	Record (map (substituteRecord s) records)
substitute s@(old, new) e@(ProjectionRecord label expr typ) =
	ProjectionRecord label (substitute s expr) typ

-- Sums
substitute s@(old, new) e@(Case expr e1@(var1, expr1) e2@(var2, expr2)) =
	Case (substitute s expr) (substituteCase s e1) (substituteCase s e2)
substitute s@(old, new) e@(LeftTag expr typ) =
	LeftTag (substitute s expr) typ
substitute s@(old, new) e@(RightTag expr typ) =
	RightTag (substitute s expr) typ

-- Variants
substitute s@(old, new) e@(CaseVariant expr alternatives) =
	CaseVariant (substitute s expr) (map (substituteCaseVariant s) alternatives)
substitute s@(old, new) e@(Tag label expr typ) =
	Tag label (substitute s expr) typ

-- Lists
substitute s@(old, new) e@(Nil _) = e
substitute s@(old, new) e@(Cons typ expr1 expr2) =
	Cons typ (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(IsNil typ expr) =
	IsNil typ (substitute s expr)
substitute s@(old, new) e@(Head typ expr) =
	Head typ (substitute s expr)
substitute s@(old, new) e@(Tail typ expr) =
	Tail typ (substitute s expr)

-- Recursive types
substitute s@(old, new) e@(Fold typ expr) =
	Fold typ (substitute s expr)
substitute s@(old, new) e@(Unfold typ expr) =
	Unfold typ (substitute s expr)

-- Type annotation
substitute s@(old, new) e@(TypeInformation typ expr) =
	TypeInformation typ $ substitute s expr

-- Casts
substitute s@(old, new) e@(Cast t1 t2 expr) =
	Cast t1 t2 $ substitute s expr

-- Blames
substitute s@(old, new) e@(Blame t1 label) = e

-- Errors
substitute s@(old, new) e@(Error msg) = e

-- substitution for case expressions
substituteCase :: ExpressionSubstitution -> (String, Expression) -> (String, Expression)
substituteCase s@(old, new) e@(var, expr)
	| old == var = e
	| otherwise = (var, substitute s expr)

-- substitution for variant case expressions
substituteCaseVariant :: ExpressionSubstitution -> Alternative -> Alternative
substituteCaseVariant s@(old, new) e@(label, var, expr)
	| old == var = e
	| otherwise = (label, var, substitute s expr)

-- substitution for records
substituteRecord :: ExpressionSubstitution -> Record -> Record
substituteRecord s@(old, new) e@(label, expr) =
	(label, substitute s expr)

-- substitute types in annotations and type information in all terms
-- using the substitutions generated during constraint unification
substituteTypedExpression :: TypeSubstitutions -> Expression -> Expression
substituteTypedExpression s = mapExpression (substituteTypedExpression' s)

-- substitute types in annotations and type information
-- using the substitutions generated during constraint unification
substituteTypedExpression' :: TypeSubstitutions -> Expression -> Expression
substituteTypedExpression' s (Ascription expr typ) =
	Ascription expr (foldr substituteType typ s)
substituteTypedExpression' s (TypeInformation typ expr) =
	TypeInformation (foldr substituteType typ s) expr
substituteTypedExpression' s e = e

-- HELPER FUNCTIONS

-- remove type information from all terms in expression
removeTypeInformation :: Expression -> Expression
removeTypeInformation = mapExpression removeTypeInformation'

-- remove type information from expression
removeTypeInformation' :: Expression -> Expression
removeTypeInformation' (TypeInformation _ expr) = expr
removeTypeInformation' (Ascription expr _) = expr
removeTypeInformation' e = e

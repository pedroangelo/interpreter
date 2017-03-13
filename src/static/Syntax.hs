module Syntax where

-- Types
import Types

-- Expressions in λ-calculus and extensions
data Expression
	-- pure λ-calculus terms
	= Variable Var
	| Abstraction Var Expression
	| Application Expression Expression
	-- Ascribed terms
	| Ascription Expression Type
	-- Annotated Abstraction
	| Annotation Var Type Expression
	-- Integers
	| Int Int
	-- Booleans
	| Bool Bool
	-- Let bindings
	| Let Var Expression Expression
	-- Fixed point
	| Fix Expression
	-- Recursive let binding
	| LetRec Var Expression Expression
	-- Conditional statement
	| If Expression Expression Expression
	-- Arithmetic Operators
	| Addition Expression Expression
	| Subtraction Expression Expression
	| Multiplication Expression Expression
	| Division Expression Expression
	-- Relational Operators
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
	-- Sums
	| Case Expression (Var, Expression) (Var, Expression)
	| LeftTag Expression Type
	| RightTag Expression Type
	-- Variants
	| CaseVariant Expression Alternatives
	| Tag Label Expression Type
	-- Recursive Types
	| Fold Type Expression
	| Unfold Type Expression
	deriving (Show, Eq)

type Alternatives = [Alternative]
type Alternative = (Label, Var, Expression)

-- MAPPING

-- Expression Mapping
mapExpression :: (Expression -> Expression) -> Expression -> Expression
mapExpression f e@(Variable var) = f e
mapExpression f e@(Abstraction var expr) = f (Abstraction var $ mapExpression f expr)
mapExpression f e@(Application expr1 expr2) = f (Application (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(Ascription expr typ) = f (Ascription (mapExpression f expr) typ)
mapExpression f e@(Annotation var typ expr) = f (Annotation var typ (mapExpression f expr))
mapExpression f e@(Int int) = f e
mapExpression f e@(Bool bool) = f e
mapExpression f e@(Let var expr1 expr2) = f (Let var (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(Fix expr) = f (Fix (mapExpression f expr))
mapExpression f e@(LetRec var expr1 expr2) = f (LetRec var (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(If expr1 expr2 expr3) = f (If (mapExpression f expr1) (mapExpression f expr2) (mapExpression f expr3))
mapExpression f e@(Addition expr1 expr2) = f (Addition (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(Subtraction expr1 expr2) = f (Subtraction (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(Multiplication expr1 expr2) = f (Multiplication (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(Division expr1 expr2) = f (Division (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(Equal expr1 expr2) = f (Equal (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(NotEqual expr1 expr2) = f (NotEqual (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(LesserThan expr1 expr2) = f (LesserThan (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(GreaterThan expr1 expr2) = f (GreaterThan (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(LesserEqualTo expr1 expr2) = f (LesserEqualTo (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(GreaterEqualTo expr1 expr2) = f (GreaterEqualTo (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(Unit) = f e
mapExpression f e@(Pair expr1 expr2) = f (Pair (mapExpression f expr1) (mapExpression f expr2))
mapExpression f e@(First expr) = f (First (mapExpression f expr))
mapExpression f e@(Second expr) = f (Second (mapExpression f expr))
mapExpression f e@(Case expr (var1, expr1) (var2, expr2)) = f (Case (mapExpression f expr) (var1, mapExpression f expr1) (var2, mapExpression f expr2))
mapExpression f e@(LeftTag expr typ) = f (LeftTag (mapExpression f expr) typ)
mapExpression f e@(RightTag expr typ) = f (RightTag (mapExpression f expr) typ)
mapExpression f e@(CaseVariant expr alternatives) =
	f (CaseVariant (mapExpression f expr)
	(map (\x -> (fst3 x, snd3 x, mapExpression f (trd3 x))) alternatives))
mapExpression f e@(Tag label expr typ) = f (Tag label (mapExpression f expr) typ)
mapExpression f e@(Fold typ expr) = f (Fold typ (mapExpression f expr))
mapExpression f e@(Unfold typ expr) = f (Unfold typ (mapExpression f expr))


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

-- check if is an ascription
isAscription :: Expression -> Bool
isAscription (Ascription _ _) = True
isAscription _ = False

-- check if is an annotated abstraction
isAnnotation :: Expression -> Bool
isAnnotation (Annotation _ _ _) = True
isAnnotation _ = False

-- check if is a boolean
isBool :: Expression -> Bool
isBool (Bool _) = True
isBool _ = False

-- check if is an integer
isInt :: Expression -> Bool
isInt (Int _) = True
isInt _ = False

-- check if is a let binding
isLet :: Expression -> Bool
isLet (Let _ _ _) = True
isLet _ = False

-- check if is a fixed point
isFix :: Expression -> Bool
isFix (Fix _) = True
isFix _ = False

-- check if is a recursive let binding
isLetRec :: Expression -> Bool
isLetRec (LetRec _ _ _) = True
isLetRec _ = False

-- check if is a conditional statement
isIf :: Expression -> Bool
isIf (If _ _ _) = True
isIf _ = False

-- check if is an addition
isAddition :: Expression -> Bool
isAddition (Addition _ _) = True
isAddition _ = False

-- check if is a subtraction
isSubtraction :: Expression -> Bool
isSubtraction (Subtraction _ _) = True
isSubtraction _ = False

-- check if is a multiplication
isMultiplication :: Expression -> Bool
isMultiplication (Multiplication _ _) = True
isMultiplication _ = False

-- check if is a division
isDivision :: Expression -> Bool
isDivision (Division _ _) = True
isDivision _ = False

-- check if is an equality check
isEqual :: Expression -> Bool
isEqual (Equal _ _) = True
isEqual _ = False

-- check if is a non equality check
isNotEqual :: Expression -> Bool
isNotEqual (NotEqual _ _) = True
isNotEqual _ = False

-- check if is a lesser than check
isLessThan :: Expression -> Bool
isLessThan (LesserThan _ _) = True
isLessThan _ = False

-- check if is a greater than check
isGreaterThan :: Expression -> Bool
isGreaterThan (GreaterThan _ _) = True
isGreaterThan _ = False

-- check if is a lesser than or equal to check
isLessEqualTo :: Expression -> Bool
isLessEqualTo (LesserEqualTo _ _) = True
isLessEqualTo _ = False

-- check if is a greater than or equal to check
isGreaterEqualTo :: Expression -> Bool
isGreaterEqualTo (GreaterEqualTo _ _) = True
isGreaterEqualTo _ = False

-- check if it an unit
isUnit :: Expression -> Bool
isUnit Unit = True
isUnit _ = False

-- check if is a pair
isPair :: Expression -> Bool
isPair (Pair _ _) = True
isPair _ = False

-- check if is a first projection
isFirst :: Expression -> Bool
isFirst (First _) = True
isFirst _ = False

-- check if is a second projection
isSecond :: Expression -> Bool
isSecond (Second _) = True
isSecond _ = False

-- check if is a case
isCase :: Expression -> Bool
isCase (Case _ _ _) = True
isCase _ = False

-- check if is a left tag
isLeftTag :: Expression -> Bool
isLeftTag (LeftTag _ _) = True
isLeftTag _ = False

-- check if is a right tag
isRightTag :: Expression -> Bool
isRightTag (RightTag _ _) = True
isRightTag _ = False

-- check if is a variant case
isCaseVariant :: Expression -> Bool
isCaseVariant (CaseVariant _ _) = True
isCaseVariant _ = False

-- check if is a tag
isTag :: Expression -> Bool
isTag (Tag _ _ _) = True
isTag _ = False

-- check if is a fold
isFold :: Expression -> Bool
isFold (Fold _ _) = True
isFold _ = False

-- check if is an unfold
isUnfold :: Expression -> Bool
isUnfold (Unfold _ _) = True
isUnfold _ = False

-- check if is a value
isValue :: Expression -> Bool
isValue e =
	isVariable e ||
	isAbstraction e ||
	isBool e ||
	isInt e ||
	isUnit e ||
	(isPair e && isValuePair e) ||
	((isLeftTag e || isRightTag e) && isValueSums e) ||
	(isTag e && isValueVariants e) ||
	isFold e

-- check if pair is a value
isValuePair :: Expression -> Bool
isValuePair (Pair expr1 expr2) = isValue expr1 && isValue expr2
isValuePair _ = False

-- check if tag is a value
isValueSums :: Expression -> Bool
isValueSums (LeftTag expr typ) = isValue expr
isValueSums (RightTag expr typ) = isValue expr
isValueSums _ = False

-- check if variant tag is a value
isValueVariants :: Expression -> Bool
isValueVariants (Tag label expr typ) = isValue expr
isValueVariants _ = False

-- check if is an arithmetic operator
isArithmeticOperator :: Expression -> Bool
isArithmeticOperator (Addition _ _) = True
isArithmeticOperator (Subtraction _ _) = True
isArithmeticOperator (Multiplication _ _) = True
isArithmeticOperator (Division _ _) = True
isArithmeticOperator _ = False

-- check if is a relational operator
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

-- SUBSTITUTIONS
type ExpressionSubstitution = (String, Expression)

-- Substitute expressions according to substitution
substitute :: ExpressionSubstitution -> Expression -> Expression

-- if the expression is a variable
substitute s@(old, new) e@(Variable var)
	-- if var equals old, replace variable with new expression
	| var == old = new
	-- otherwise, replace nothing
	| otherwise = e

-- if the expression is an abstraction
substitute s@(old, new) e@(Abstraction var expr)
	-- if some abstraction has already binded the variable, don't propagate substitutions
	| var == old = e
	-- otherwise, propagate substitutions
	| otherwise = Abstraction var $ substitute s expr

-- if the expression is an application
substitute s@(old, new) e@(Application expr1 expr2) =
	-- propagate substitutions
	Application (substitute s expr1) (substitute s expr2)

-- if the expression is an ascription
substitute s@(old, new) e@(Ascription expr typ) =
	-- propagate substitutions
	Ascription (substitute s expr) typ

-- if the expression is an annotated Abstraction
substitute s@(old, new) e@(Annotation var typ expr)
	-- if some abstraction has already binded the variable, don't propagate substitutions
	| var == old = e
	-- otherwise, propagate substitutions
	| otherwise = Annotation var typ $ substitute s expr

-- if the expression is a base type such as Int or Bool, do nothing
substitute s@(old, new) e@(Bool _) = e
substitute s@(old, new) e@(Int _) = e

-- if the expression is a let binding
substitute s@(old, new) e@(Let var expr1 expr2)
	-- if let has already binded the variable, dont propagate substitutions
	| var == old = e
	-- otherwise, propagate substitutions
	| otherwise = Let var (substitute s expr1) (substitute s expr2)

-- if the expression is a fixed point, propagate substitutions
substitute s@(old, new) e@(Fix expr) = Fix $ substitute s expr

-- if the expression is a recursive let binding
substitute s@(old, new) e@(LetRec var expr1 expr2)
	-- if let has already binded the variable, dont propagate substitutions
	| var == old = e
	-- otherwise, propagate substitutions
	| otherwise = LetRec var (substitute s expr1) (substitute s expr2)

-- if the expression is a conditional statement
substitute s@(old, new) e@(If expr1 expr2 expr3) =
	-- propagate substitutions
	If (substitute s expr1) (substitute s expr2) (substitute s expr3)

-- if expression is an arithmetic operation or comparison operator,
-- propagate substitutions
substitute s@(old, new) e@(Addition expr1 expr2) =
	Addition (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(Subtraction expr1 expr2) =
	Subtraction (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(Multiplication expr1 expr2) =
	Multiplication (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(Division expr1 expr2) =
	Division (substitute s expr1) (substitute s expr2)
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

-- if expression is an unit
substitute s@(old, new) e@(Unit) = e

-- if the expression is a pair or a projection
substitute s@(old, new) e@(Pair expr1 expr2) =
	Pair (substitute s expr1) (substitute s expr2)
substitute s@(old, new) e@(First expr) =
	First (substitute s expr)
substitute s@(old, new) e@(Second expr) =
	Second (substitute s expr)

-- if the expression is a case or tag
substitute s@(old, new) e@(Case expr e1@(var1, expr1) e2@(var2, expr2)) =
	Case (substitute s expr) (substituteCase s e1) (substituteCase s e2)
substitute s@(old, new) e@(LeftTag expr typ) =
	LeftTag (substitute s expr) typ
substitute s@(old, new) e@(RightTag expr typ) =
	RightTag (substitute s expr) typ

-- if the expression is a variant case or tag
substitute s@(old, new) e@(CaseVariant expr alternatives) =
	CaseVariant (substitute s expr) (map (substituteCaseVariant s) alternatives)
substitute s@(old, new) e@(Tag label expr typ) =
	Tag label (substitute s expr) typ

-- if the expression is a fold or unfold
substitute s@(old, new) e@(Fold typ expr) =
	Fold typ (substitute s expr)
substitute s@(old, new) e@(Unfold typ expr) =
	Unfold typ (substitute s expr)

-- substitution for case expressions
substituteCase :: ExpressionSubstitution -> (String, Expression) -> (String, Expression)
substituteCase s@(old, new) e@(var, expr)
	| old == var = e
	| otherwise = (var, substitute s expr)

-- substitution for case expressions
substituteCaseVariant :: ExpressionSubstitution -> Alternative -> Alternative
substituteCaseVariant s@(old, new) e@(label, var, expr)
	| old == var = e
	| otherwise = (label, var, substitute s expr)

-- HELPER FUNCTIONS

fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

snd3 :: (a, b, c) -> b
snd3 (_, b, _) = b

trd3 :: (a, b, c) -> c
trd3 (_, _, c) = c

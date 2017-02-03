module Syntax where

-- Types
import Types

-- Expressions in λ-calculus and extensions
data Expression
	= Variable String
	| Abstraction String Expression
	| Application Expression Expression
	| Ascription Expression Type
	| Annotation String Type Expression
	| Int Int
	| Bool Bool
	| Let String Expression Expression
	| Fix Expression
	| LetRec String Expression Expression
	| If Expression Expression Expression
	| Addition Expression Expression
	| Subtraction Expression Expression
	| Multiplication Expression Expression
	| Division Expression Expression
	| Equal Expression Expression
	| NotEqual Expression Expression
	| LesserThan Expression Expression
	| GreaterThan Expression Expression
	| LesserEqualTo Expression Expression
	| GreaterEqualTo Expression Expression
	| TypeInformation Type Expression
	deriving (Show, Eq)

-- HELPER FUNCTIONS

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

-- check if is a type information
isTypeInformation :: Expression -> Bool
isTypeInformation (TypeInformation _ _) = True
isTypeInformation _ = False

-- check if is a value
isValue :: Expression -> Bool
isValue e =
	isVariable e ||
	isAbstraction e ||
	isAnnotation e ||
	isBool e ||
	isInt e

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

-- if expression is a type information, propagate substitutions
substitute s@(old, new) e@(TypeInformation typ expr) =
	TypeInformation typ $ substitute s expr

-- substitute types in annotations and type information
-- using the substitutions generated during constraint unification
substituteTypedExpression :: TypeSubstitutions -> Expression -> Expression
substituteTypedExpression s (Variable var) = Variable var
substituteTypedExpression s (Abstraction var expr) =
	Abstraction var $ substituteTypedExpression s expr
substituteTypedExpression s (Application expr1 expr2) =
	Application (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (Ascription expr typ) =
	Ascription (substituteTypedExpression s expr) (insertTypeParameters $ foldr instantiateTypeVariable typ s)
substituteTypedExpression s (Annotation var typ expr) =
	Annotation var typ (substituteTypedExpression s expr)
substituteTypedExpression s (Int int) =	Int int
substituteTypedExpression s (Bool bool) = Bool bool
substituteTypedExpression s (Let var expr1 expr2) =
	Let var (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (Fix expr) =
	Fix (substituteTypedExpression s expr)
substituteTypedExpression s (LetRec var expr1 expr2) =
	LetRec var (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (If expr1 expr2 expr3) =
	If (substituteTypedExpression s expr1) (substituteTypedExpression s expr2) (substituteTypedExpression s expr3)
substituteTypedExpression s (Addition expr1 expr2) =
	Addition (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (Subtraction expr1 expr2) =
	Subtraction (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (Multiplication expr1 expr2) =
	Multiplication (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (Division expr1 expr2) =
	Division (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (Equal expr1 expr2) =
	Equal (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (NotEqual expr1 expr2) =
	NotEqual (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (LesserThan expr1 expr2) =
	LesserThan (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (GreaterThan expr1 expr2) =
	GreaterThan (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (LesserEqualTo expr1 expr2) =
	LesserEqualTo (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (GreaterEqualTo expr1 expr2) =
	GreaterEqualTo (substituteTypedExpression s expr1) (substituteTypedExpression s expr2)
substituteTypedExpression s (TypeInformation typ expr) =
	TypeInformation (insertTypeParameters $ foldr instantiateTypeVariable typ s) (substituteTypedExpression s expr)

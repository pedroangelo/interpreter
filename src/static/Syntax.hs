module Syntax where

-- Expressions in λ-calculus and extensions
data Expression
	= Variable String
	| Abstraction String Expression
	| Application Expression Expression
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
	| Error String
	deriving (Show, Eq)

-- HELPER FUNCTIONS

-- check if is a variable
isVariable :: Expression -> Bool
isVariable (Variable _) = True
isVariable _ = False

-- check if is a abstraction
isAbstraction :: Expression -> Bool
isAbstraction (Abstraction _ _) = True
isAbstraction _ = False

-- check if is a application
isApplication :: Expression -> Bool
isApplication (Application _ _) = True
isApplication _ = False

-- check if is a boolean
isBool :: Expression -> Bool
isBool (Bool _) = True
isBool _ = False

-- check if is a integer
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

-- check if is a addition
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

-- check if is a equality check
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

-- check if is a error
isError :: Expression -> Bool
isError (Error _) = True
isError _ = False

-- check if is a value
isValue :: Expression -> Bool
isValue e =
	isVariable e ||
	isAbstraction e ||
	isBool e ||
	isInt e

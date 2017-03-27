module PrettyPrinter (
	printExpression,
	printType
) where

-- Syntax & Types
import Syntax
import Types

-- Imports
import Data.List

printExpression :: Expression -> String
printExpression e@(Variable var) =
	var
printExpression e@(Abstraction var expr) =
	"\\" ++ var ++ " . " ++ printExpression expr
printExpression e@(Application expr1 expr2) =
	"(" ++ printExpression expr1 ++ ") (" ++ printExpression expr2 ++ ")"
printExpression e@(Ascription expr typ) =
	"(" ++ printExpression expr ++ ") :: " ++ printType typ
printExpression e@(Annotation var typ expr) =
	"\\" ++ var ++ " : " ++ printType typ ++ " . " ++ printExpression expr
printExpression e@(Bool b) = show b
printExpression e@(Int i) = show i
printExpression e@(Let var expr1 expr2) =
	"let " ++ var ++ " = " ++ printExpression expr1 ++ " in " ++ printExpression expr2
printExpression e@(Fix expr) =
	"fix " ++ "(" ++ printExpression expr ++ ")"
printExpression e@(LetRec var expr1 expr2) =
	"letrec " ++ var ++ " = " ++ printExpression expr1 ++ " in " ++ printExpression expr2
printExpression e@(If expr1 expr2 expr3) =
	"if" ++ "(" ++ printExpression expr1 ++ ") then ("
		++ printExpression expr2 ++ ") else (" ++ printExpression expr3 ++ ")"
printExpression e@(Addition expr1 expr2) =
	"(" ++ printExpression expr1 ++ ") + (" ++ printExpression expr2 ++ ")"
printExpression e@(Subtraction expr1 expr2) =
	"(" ++ printExpression expr1 ++ ") - (" ++ printExpression expr2 ++ ")"
printExpression e@(Multiplication expr1 expr2) =
	"(" ++ printExpression expr1 ++ ") * (" ++ printExpression expr2 ++ ")"
printExpression e@(Division expr1 expr2) =
	"(" ++ printExpression expr1 ++ ") / (" ++ printExpression expr2 ++ ")"
printExpression e@(Equal expr1 expr2) =
	"(" ++ printExpression expr1 ++ ") == (" ++ printExpression expr2 ++ ")"
printExpression e@(NotEqual expr1 expr2) =
	"(" ++ printExpression expr1 ++ ") /= (" ++ printExpression expr2 ++ ")"
printExpression e@(LesserThan expr1 expr2) =
	"(" ++ printExpression expr1 ++ ") < (" ++ printExpression expr2 ++ ")"
printExpression e@(GreaterThan expr1 expr2) =
	"(" ++ printExpression expr1 ++ ") > (" ++ printExpression expr2 ++ ")"
printExpression e@(LesserEqualTo expr1 expr2) =
	"(" ++ printExpression expr1 ++ ") <= (" ++ printExpression expr2 ++ ")"
printExpression e@(GreaterEqualTo expr1 expr2) =
	"(" ++ printExpression expr1 ++ ") >= (" ++ printExpression expr2 ++ ")"
printExpression e@(Unit) = "()"
printExpression e@(Pair expr1 expr2) =
	"(" ++ printExpression expr1 ++ "," ++ printExpression expr2 ++ ")"
printExpression e@(First expr) =
	"(" ++ printExpression expr ++ ").1"
printExpression e@(Second expr) =
	"(" ++ printExpression expr ++ ").2"
printExpression e@(Record records) =
	"{" ++ (concat $ intersperse ", " $
		map (\x -> (fst x) ++ " = " ++ printExpression (snd x)) records) ++ "}"
printExpression e@(ProjectionRecord label expr typ) =
	"(" ++ printExpression expr ++ ")." ++ label
printExpression e@(Case expr (var1, expr1) (var2, expr2)) =
	"case (" ++ printExpression expr ++ ") of \n  " ++
		"inl " ++ var1 ++ " => " ++ printExpression expr1 ++ " \n| " ++
		"inr " ++ var2 ++ " => " ++ printExpression expr2
printExpression e@(LeftTag expr typ) =
	"inl (" ++ printExpression expr ++ ")"
printExpression e@(RightTag expr typ) =
	"inr (" ++ printExpression expr ++ ")"
printExpression e@(CaseVariant expr alternatives) =
	"case (" ++ printExpression expr ++ ") of \n  " ++
		(concat $ intersperse " \n| " $ map
			(\x -> (fst3 x) ++ " " ++ (snd3 x) ++ " => " ++ printExpression (trd3 x))
			alternatives)
printExpression e@(Tag label expr typ) =
	"<" ++ label ++ "=" ++ printExpression expr ++ ">"
printExpression e@(Fold typ expr) =
	"fold " ++ printExpression expr
printExpression e@(Unfold typ expr) =
	"unfold " ++ printExpression expr
printExpression e@(TypeInformation typ expr) =
	printExpression expr ++ " : " ++ printType typ
printExpression e@(Cast typ1 typ2 expr) =
	printExpression expr ++ " : " ++ printType typ1 ++ " => " ++ printType typ2
printExpression e@(Blame typ msg) = msg
printExpression e@(Error msg) = msg

printType :: Type -> String
printType t@(VarType var) =
	var
printType t@(ArrowType t1 t2) =
	"(" ++ printType t1 ++ ")" ++ " -> " ++ printType t2
printType t@(IntType) = "Int"
printType t@(BoolType) = "Bool"
printType t@(DynType) = "?"
printType t@(ForAll var typ) =
	"∀" ++ var ++ "." ++ printType typ
printType t@(UnitType) = "()"
printType t@(ProductType t1 t2) =
	"(" ++ printType t1 ++ " × " ++ printType t2 ++ ")"
printType t@(RecordType ts) =
	"{" ++ (concat $ intersperse ", " $
		map (\x -> (fst x) ++ " : " ++ printType (snd x)) ts) ++ "}"
printType t@(SumType t1 t2) =
	"(" ++ printType t1 ++ " + " ++ printType t2 ++ ")"
printType t@(VariantType ts) =
	"<" ++ (concat $ intersperse ", " $
		map (\x -> (fst x) ++ " : " ++ printType (snd x)) ts) ++ ">"
printType t@(Mu var typ) =
	"μ" ++ var ++ "." ++ printType typ

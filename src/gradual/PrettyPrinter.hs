module PrettyPrinter (
	prettyExpression,
	prettyType
) where

-- Syntax & Types
import Syntax
import Types

-- Imports
import Data.List
import Text.PrettyPrint.Leijen

prettyExpression :: Expression -> Doc
prettyExpression (Variable var) = text var
prettyExpression (Abstraction var expr) = hcat
	[text "\\", text var, text " . ", prettyExpression expr]
prettyExpression (Application expr1 expr2) = hsep
	[printParensExpression expr1, printParensExpression expr2]
prettyExpression (Ascription expr typ) = hcat
	[prettyExpression expr, text " :: ", prettyType typ]
prettyExpression (Annotation var typ expr) = hcat
	[text "\\", text var, text " : ", prettyType typ, text " . ", prettyExpression expr]
prettyExpression (Int i) = int i
prettyExpression (Bool b) = text $ show b
prettyExpression (Let var expr1 expr2) = hsep
	[text "let", text var, text "=", prettyExpression expr1, text "in"] <$$>
	prettyExpression expr2
prettyExpression (Fix expr) = hsep
	[text "fix", printParensExpression expr]
prettyExpression (LetRec var expr1 expr2) = hsep
	[text "letrec", text var, text "=", prettyExpression expr1, text "in"] <$$>
	prettyExpression expr2
prettyExpression (If expr1 expr2 expr3) = nest 2 $ sep
	[text "if" <+> prettyExpression expr1,
	text "then" <+> prettyExpression expr2,
	text "else" <+> prettyExpression expr3]
prettyExpression (Addition expr1 expr2) = hsep
	[printParensExpression expr1, text "+", printParensExpression expr2]
prettyExpression (Subtraction expr1 expr2) = hsep
	[printParensExpression expr1, text "-", printParensExpression expr2]
prettyExpression (Multiplication expr1 expr2) = hsep
	[printParensExpression expr1, text "*", printParensExpression expr2]
prettyExpression (Division expr1 expr2) = hsep
	[printParensExpression expr1, text "/", printParensExpression expr2]
prettyExpression (Equal expr1 expr2) = hsep
	[printParensExpression expr1, text "==", printParensExpression expr2]
prettyExpression (NotEqual expr1 expr2) = hsep
	[printParensExpression expr1, text "/=", printParensExpression expr2]
prettyExpression (LesserThan expr1 expr2) = hsep
	[printParensExpression expr1, text "<", printParensExpression expr2]
prettyExpression (GreaterThan expr1 expr2) = hsep
	[printParensExpression expr1, text ">", printParensExpression expr2]
prettyExpression (LesserEqualTo expr1 expr2) = hsep
	[printParensExpression expr1, text "<=", printParensExpression expr2]
prettyExpression (GreaterEqualTo expr1 expr2) = hsep
	[printParensExpression expr1, text ">=", printParensExpression expr2]
prettyExpression (Unit) = text "unit"
prettyExpression (Pair expr1 expr2) = parens $ hcat $
	punctuate comma [prettyExpression expr1, prettyExpression expr2]
prettyExpression (First expr) =	hcat
	[printParensExpression expr, text ".1"]
prettyExpression (Second expr) = hcat
	[printParensExpression expr, text ".2"]
prettyExpression (Tuple exprs) = parens $ hcat $
	punctuate comma $ map prettyExpression exprs
prettyExpression (ProjectionTuple index expr typ) = hcat
	[printParensExpression expr, text ".", int index]
prettyExpression (Record records) = braces $ hcat $ punctuate (comma <> space) $
		map (\x -> text (fst x) <> text "=" <> prettyExpression (snd x)) records
prettyExpression (ProjectionRecord label expr typ) = hcat
	[printParensExpression expr, text ".", text label]
prettyExpression (Case expr (var1, expr1) (var2, expr2)) = nest 2 $ vsep
	[text "case" <+> printParensExpression expr <+> text "of",
	nest 2 $ text "| inl" <+> text var1 <+> text "=>" <+> prettyExpression expr1,
	nest 2 $ text "| inr" <+> text var2 <+> text "=>" <+> prettyExpression expr2]
prettyExpression (LeftTag expr typ) = hsep
	[text "inl", printParensExpression expr]
prettyExpression (RightTag expr typ) = hsep
	[text "inr", printParensExpression expr]
prettyExpression (CaseVariant expr alternatives) = nest 2 $ vsep
	[text "case" <+> printParensExpression expr <+> text "of",
	vcat (map (\x -> nest 2 $ hcat
		[text "| <", text (fst3 x),	text "=", text (snd3 x), text "> => ",
		prettyExpression (trd3 x)]) alternatives)]
prettyExpression (Tag label expr typ) = variant $ hcat
	[text label, text "=", prettyExpression expr]
prettyExpression (Fold typ expr) = hsep
	[text "fold", printParensExpression expr]
prettyExpression (Unfold typ expr) = hsep
	[text "unfold", printParensExpression expr]
prettyExpression (TypeInformation typ expr) = hsep
	[printParensExpression expr, text ":", prettyType typ]
prettyExpression (Cast t1 t2 expr) = hsep
	[printParensExpression expr, text ":", printParensType t1, text "=>", printParensType t2]
prettyExpression (Blame typ msg) = hsep
	[text "Blame:", text msg]
prettyExpression (Error msg) = hsep
	[text "Error:", text msg]

prettyType :: Type -> Doc
prettyType (VarType var) = text var
prettyType (ArrowType t1 t2) = hsep
	[printParensType t1, text "->", prettyType t2]
prettyType (IntType) = text "int"
prettyType (BoolType) = text "bool"
prettyType (DynType) = text "?"
prettyType (ForAll var typ) = hcat
	[text "forall", text var, text ".", prettyType typ]
prettyType (UnitType) = text "()"
prettyType (ProductType t1 t2) = hsep
	[printParensType t1, text "×", printParensType t2]
prettyType (TupleType ts) = parens $ hcat $ punctuate comma $ map prettyType ts
prettyType (RecordType ts) = braces $ hcat $ punctuate (comma <> space) $
		map (\x -> text (fst x) <> text ":" <> prettyType (snd x)) ts
prettyType (SumType t1 t2) = hsep
	[printParensType t1, text "+", printParensType t2]
prettyType (VariantType ts) = variant $ hcat $ punctuate (comma <> space) $
		map (\x -> text (fst x) <> text ":" <> prettyType (snd x)) ts
prettyType (Mu var typ) = hcat
	[text "mu", text var, text ".", prettyType typ]

variant :: Doc -> Doc
variant p = enclose langle rangle p

printParensExpression :: Expression -> Doc
printParensExpression expr = if needsParensExpression expr
	then parens (prettyExpression expr)
	else prettyExpression expr

needsParensExpression :: Expression -> Bool
needsParensExpression expr =
	isAbstraction expr ||
	isApplication expr ||
	isAscription expr ||
	isAnnotation expr ||
	isLet expr ||
	isFix expr ||
	isLetRec expr ||
	isIf expr ||
	isArithmeticOperator expr ||
	isRelationalOperator expr ||
	isCase expr ||
	isLeftTag expr ||
	isRightTag expr ||
	isFold expr ||
	isUnfold expr ||
	isTypeInformation expr ||
	isCast expr ||
	isBlame expr ||
	isError expr

printParensType :: Type -> Doc
printParensType typ = if needsParensType typ
	then parens (prettyType typ)
	else prettyType typ

needsParensType :: Type -> Bool
needsParensType typ =
	isArrowType typ ||
	isForAllType typ ||
	isProductType typ ||
	isSumType typ ||
	isMuType typ

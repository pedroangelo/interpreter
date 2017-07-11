module Gradual.PrettyPrinter (
    prettyExpression,
    prettyType
) where

-- Syntax & Types
import Gradual.Syntax
import Gradual.Types

-- Imports
import Data.List
import Text.PrettyPrint.Leijen

-- pretty print expression
prettyExpression :: Expression -> Doc

-- Pure λ-calculus terms
prettyExpression (Variable var) = text var
prettyExpression (Abstraction var expr) = hcat
    [backslash, text var, space, dot, space, prettyExpression expr]
prettyExpression (Application expr1 expr2) = hsep
    [printParensExpression expr1, printParensExpression expr2]

-- Ascribed terms
prettyExpression (Ascription expr typ) = hcat
    [printParensExpression expr, colon, colon, prettyType typ]

-- Annotated abstractions
prettyExpression (Annotation var typ expr) = hcat
    [backslash, text var, space, colon, space, prettyType typ, space, dot,
        space, prettyExpression expr]

-- Integers
prettyExpression (Int i) = int i

-- Booleans
prettyExpression (Bool b) = text $ show b

-- Let bindings
prettyExpression (Let var expr1 expr2) = hsep
    [text "let", text var, equals, prettyExpression expr1, text "in"] <$$>
    prettyExpression expr2

-- Fixed point
prettyExpression (Fix expr) = hsep
    [text "fix", printParensExpression expr]

-- Recursive let bindings
prettyExpression (LetRec var expr1 expr2) = hsep
    [text "letrec", text var, equals, prettyExpression expr1, text "in"] <$$>
    prettyExpression expr2

-- Conditional statements
prettyExpression (If expr1 expr2 expr3) = nest 2 $ sep
    [text "if" <+> prettyExpression expr1,
    text "then" <+> prettyExpression expr2,
    text "else" <+> prettyExpression expr3]

-- Arithmetic operators
prettyExpression (Addition expr1 expr2) = hsep
    [printParensExpression expr1, text "+", printParensExpression expr2]
prettyExpression (Subtraction expr1 expr2) = hsep
    [printParensExpression expr1, text "-", printParensExpression expr2]
prettyExpression (Multiplication expr1 expr2) = hsep
    [printParensExpression expr1, text "*", printParensExpression expr2]
prettyExpression (Division expr1 expr2) = hsep
    [printParensExpression expr1, text "/", printParensExpression expr2]

-- Relational operators
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

-- Unit
prettyExpression Unit = text "unit"

-- Pairs
prettyExpression (Pair expr1 expr2) = parens $ hcat $
    punctuate comma [prettyExpression expr1, prettyExpression expr2]
prettyExpression (First expr) =    hcat
    [printParensExpression expr, text ".1"]
prettyExpression (Second expr) = hcat
    [printParensExpression expr, text ".2"]

-- Tuples
prettyExpression (Tuple exprs) = parens $ hcat $
    punctuate comma $ map prettyExpression exprs
prettyExpression (ProjectionTuple index expr typ) = hcat
    [printParensExpression expr, dot, int index, space, text "as", space, prettyType typ]

-- Records
prettyExpression (Record records) = braces $ hcat $ punctuate (comma <> space) $
        map (\x -> text (fst x) <> equals <> prettyExpression (snd x)) records
prettyExpression (ProjectionRecord label expr typ) = hcat
    [printParensExpression expr, dot, text label, space, text "as", space, prettyType typ]

-- Sums
prettyExpression (Case expr (var1, expr1) (var2, expr2)) = nest 2 $ vsep
    [text "case" <+> prettyExpression expr <+> text "of",
    nest 2 $ text "| inl" <+> text var1 <+> text "=>" <+> prettyExpression expr1,
    nest 2 $ text "| inr" <+> text var2 <+> text "=>" <+> prettyExpression expr2]
prettyExpression (LeftTag expr typ) = hsep
    [text "inl", printParensExpression expr, text "as", prettyType typ]
prettyExpression (RightTag expr typ) = hsep
    [text "inr", printParensExpression expr, text "as", prettyType typ]

-- Variants
prettyExpression (CaseVariant expr alternatives) = nest 2 $ vsep
    [text "case" <+> prettyExpression expr <+> text "of",
    vcat (map (\x -> nest 2 $ hsep
        [text "|", text (fst3 x), text (snd3 x), text "->",
        prettyExpression (trd3 x)]) alternatives)]
prettyExpression (Tag label expr typ) = hsep
    [variant $ hcat [text label, equals, printParensExpression expr],
    text "as", prettyType typ]


-- Lists
prettyExpression (Nil typ) = hsep [text "nil", brackets $ prettyType typ]
prettyExpression (Cons typ expr1 expr2) = hcat
    [printParensExpression expr1, colon, printParensExpression expr2,
    space, text "as", space, prettyType typ]
prettyExpression (IsNil typ expr) = hsep
    [text "isnil", brackets $ prettyType typ, printParensExpression expr]
prettyExpression (Head typ expr) = hsep
    [text "head", brackets $ prettyType typ, printParensExpression expr]
prettyExpression (Tail typ expr) = hsep
    [text "tail", brackets $ prettyType typ, printParensExpression expr]

-- Recursive types
prettyExpression (Fold typ expr) = hsep
    [text "fold", brackets $ prettyType typ, printParensExpression expr]
prettyExpression (Unfold typ expr) = hsep
    [text "unfold", brackets $ prettyType typ, printParensExpression expr]

-- Type annotations
prettyExpression (TypeInformation typ expr) = hsep
    [printParensExpression expr, colon, prettyType typ]

-- Casts
prettyExpression (Cast t1 t2 expr) = hsep
    [printParensExpression expr, colon, printParensType t1, text "=>", printParensType t2]

-- Blames
prettyExpression (Blame typ msg) = hsep
    [text "Blame:", text msg]

-- Errors
prettyExpression (Error msg) = hsep
    [text "Error:", text msg]

-- pretty print type
prettyType :: Type -> Doc

-- Type variable: Var
prettyType (VarType var) = text var

-- Arrow type: Type -> Type
prettyType (ArrowType t1 t2) = hsep
    [printParensType t1, text "->", prettyType t2]

-- Integer type: Int
prettyType IntType = text "Int"

-- Boolean type: Bool
prettyType BoolType = text "Bool"

-- Dynamic type: ?
prettyType DynType = text "Dyn"

-- For all quantifier: forall Var.Type
prettyType (ForAll var typ) = hsep
    [text "forall", text var, text ".", prettyType typ]

-- Unit type: Unit
prettyType UnitType = text "Unit"

-- Product type: Type × Type
prettyType (ProductType t1 t2) = hsep
    [printParensType t1, text "×", printParensType t2]

-- Tuple type: (Types)
prettyType (TupleType ts) = parens $ hcat $ punctuate comma $ map prettyType ts

-- Record type: {Labels:Types}
prettyType (RecordType ts) = braces $ hcat $ punctuate (comma <> space) $
        map (\x -> text (fst x) <> colon <> prettyType (snd x)) ts

-- Sum type: Type + Type
prettyType (SumType t1 t2) = hsep
    [printParensType t1, text "+", printParensType t2]

-- Variant type: <Labels:Types>
prettyType (VariantType ts) = variant $ hcat $ punctuate (comma <> space) $
        map (\x -> text (fst x) <> colon <> prettyType (snd x)) ts

-- List type: [Type]
prettyType (ListType t) = brackets $ prettyType t

-- Recursive type: mu Var.Type
prettyType (Mu var typ) = hsep
    [text "rec", text var, dot, prettyType typ]

variant :: Doc -> Doc
variant = enclose langle rangle

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
    isProjectionTuple expr ||
    isProjectionRecord expr ||
    isCase expr ||
    isLeftTag expr ||
    isRightTag expr ||
    isCaseVariant expr ||
    isNil expr ||
    isCons expr ||
    isIsNil expr ||
    isHead expr ||
    isTail expr ||
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

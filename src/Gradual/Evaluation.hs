module Gradual.Evaluation (
    evaluate
) where

-- Syntax & Types
import Gradual.Syntax
import Gradual.Types
import Gradual.Examples

-- Imports
import Data.Maybe

evaluationStyle = evaluate

-- evaluate using call-by-value strategy
evaluate :: Expression -> Expression

-- variables are values
evaluate e@(Variable _) = e

-- abstractions are values
evaluate e@(Abstraction _ _) = e

-- if expression is an application
evaluate e@(Application expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ Application v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ Application expr1 v2
    -- C-BETA - simulate casts on data types
    | isCast expr1 =
        let
            (Cast t1 t2 expr1') = expr1
            (ArrowType t11 t12) = t1
            (ArrowType t21 t22) = t2
            expr2' = Cast t21 t11 expr2
        in evaluationStyle $ Cast t12 t22 $ Application expr1' expr2'
    -- beta reduction
    | isAbstraction expr1 && isValue expr2 =
        let (Abstraction var expr) = expr1
        in evaluationStyle $ substitute (var, expr2) expr

-- if expression is an ascription
evaluate e@(Ascription expr typ)
    -- push blames to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- remove ascription
    | isValue expr = evaluationStyle $ expr
    | otherwise =
        let v1 = evaluate expr
        in evaluationStyle $ Ascription v1 typ

-- if expression is an annotated abstraction
evaluate e@(Annotation var typ expr) =
    -- remove type
    Abstraction var expr

-- booleans are values
evaluate e@(Bool _) = e

-- integers are values
evaluate e@(Int _) = e

-- if expression is let binding
evaluate e@(Let var expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ Let var v1 expr2
    -- substitute ocurrences of var in expr2 by expr1
    | otherwise = evaluationStyle $ substitute (var, expr1) expr2

-- if expression is fixed point
evaluate e@(Fix expr)
    -- push blames to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr
    | not $ isValue expr =
        let v = evaluate expr
        in evaluationStyle $ Fix v
    -- C-FIX - simulate casts on data types
    | isCast expr =
        let
            (Cast t1 t2 expr') = expr
            (ArrowType t11 t12) = t1
            (ArrowType t21 t22) = t2
        in evaluationStyle $ Cast t11 t21 $ Fix expr'
    -- substitute abstraction variable with e in expr
    | isAbstraction expr =
        let (Abstraction var expr') = expr
        in evaluationStyle $ substitute (var, e) expr'

-- if expression is a recursive let binding
evaluate e@(LetRec var expr1 expr2) =
    -- derive form into a let binding
    evaluationStyle $ Let var (Fix $ Abstraction var expr1) expr2

-- if expression is a conditional statement
evaluate e@(If expr1 expr2 expr3)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    | isBlame expr3 = expr3
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    | isError expr3 = expr3
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ If v1 expr2 expr3
    -- if expr1 is True, evaluate expr2
    | expr1 == Bool True = evaluationStyle expr2
    --- if expr1 is False, evaluate expr3
    | expr1 == Bool False = evaluationStyle expr3

-- if expression is a addition
evaluate e@(Addition expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ Addition v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ Addition expr1 v2
    -- call native addition function between expr1 and expr2
    | otherwise =
        let
            Int i1 = expr1
            Int i2 = expr2
        in Int (i1 + i2)

-- if expression is a subtraction
evaluate e@(Subtraction expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ Subtraction v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ Subtraction expr1 v2
    -- call native subtraction function between expr1 and expr2
    | otherwise =
        let
            Int i1 = expr1
            Int i2 = expr2
        in Int (i1 - i2)

-- if expression is a multiplication
evaluate e@(Multiplication expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ Multiplication v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ Multiplication expr1 v2
    -- call native multiplication function between expr1 and expr2
    | otherwise =
        let
            Int i1 = expr1
            Int i2 = expr2
        in Int (i1 * i2)

-- if expression is a division
evaluate e@(Division expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ Division v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ Division expr1 v2
    -- call native division function between expr1 and expr2
    | otherwise =
        let
            Int i1 = expr1
            Int i2 = expr2
        in Int $ div i1 i2

-- if expression is a equality check
evaluate e@(Equal expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ Equal v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ Equal expr1 v2
    -- call native equality check between expr1 and expr2
    | otherwise =
        let
            Int i1 = expr1
            Int i2 = expr2
        in Bool (i1 == i2)

-- if expression is a non equality check
evaluate e@(NotEqual expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ NotEqual v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ NotEqual expr1 v2
    -- call native non equality check between expr1 and expr2
    | otherwise =
        let
            Int i1 = expr1
            Int i2 = expr2
        in Bool (i1 /= i2)

-- if expression is a lesser than check
evaluate e@(LesserThan expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ LesserThan v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ LesserThan expr1 v2
    -- call native lesser than check between expr1 and expr2
    | otherwise =
        let
            Int i1 = expr1
            Int i2 = expr2
        in Bool (i1 < i2)

-- if expression is a greater than check
evaluate e@(GreaterThan expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ GreaterThan v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ GreaterThan expr1 v2
    -- call native greater than check between expr1 and expr2
    | otherwise =
        let
            Int i1 = expr1
            Int i2 = expr2
        in Bool (i1 > i2)

-- if expression is a lesser than or equal to check
evaluate e@(LesserEqualTo expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ LesserEqualTo v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ LesserEqualTo expr1 v2
    -- call native lesser than or equal to check between expr1 and expr2
    | otherwise =
        let
            Int i1 = expr1
            Int i2 = expr2
        in Bool (i1 <= i2)

-- if expression is a greater than or equal to check
evaluate e@(GreaterEqualTo expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ GreaterEqualTo v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ GreaterEqualTo expr1 v2
    -- call native greater than or equal to check between expr1 and expr2
    | otherwise =
        let
            Int i1 = expr1
            Int i2 = expr2
        in Bool (i1 >= i2)

-- if expression is an unit
evaluate e@(Unit) = e

-- if expression is a pair
evaluate e@(Pair expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ Pair v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ Pair expr1 v2
    | otherwise = e

-- if expression is a first projection
evaluate e@(First expr)
    -- push blames to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr
    | not $ isValue expr =
        let v = evaluate expr
        in evaluationStyle $ First v
    -- project first element of pair
    | isPair expr =
        let (Pair expr1 expr2) = expr
        in evaluationStyle $ expr1
    -- C-FIRST - simulate casts on data types
    | isCast expr =
        let
            (Cast t1 t2 expr') = expr
            (ProductType t11 t12) = t1
            (ProductType t21 t22) = t2
        in evaluationStyle $ Cast t11 t21 $ First expr'

-- if expression is a second projection
evaluate e@(Second expr)
    -- push blames to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr
    | not $ isValue expr =
        let v = evaluate expr
        in evaluationStyle $ Second v
    -- project second element of pair
    | isPair expr =
        let (Pair expr1 expr2) = expr
        in evaluationStyle $ expr2
    -- C-SECOND - simulate casts on data types
    | isCast expr =
        let
            (Cast t1 t2 expr') = expr
            (ProductType t11 t12) = t1
            (ProductType t21 t22) = t2
        in evaluationStyle $ Cast t12 t22 $ Second expr'

-- if expression is a tuple
evaluate e@(Tuple exprs)
    -- push blames to the top level
    | any isBlame $ exprs =
        let    blames = filter isBlame exprs
        in head blames
    -- push errors to the top level
    | any isError $ exprs =
        let    errors = filter isError exprs
        in head errors
    -- reduce expressions
    | any (not . isValue) exprs =
        let    exprs' = map evaluate exprs
        in Tuple exprs'
    | otherwise = e

-- if expression is a projection from tuple
evaluate e@(ProjectionTuple index expr typ)
    -- push blames to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr
    | not $ isValue expr =
        let v = evaluate expr
        in evaluationStyle $ ProjectionTuple index v typ
    -- project element of tuple
    | isTuple expr =
        let
            Tuple exprs = expr
            expr' = exprs !! index
        in evaluationStyle expr'
    -- C-ProjectionTuple - simulate casts on data types
    | isCast expr =
        let
            (Cast t1 t2 expr') = expr
            -- get types from record
            TupleType list1 = t1
            TupleType list2 = t2
            t' = list1 !! index
            t'' = list2 !! index
        in evaluationStyle $ Cast t' t'' $ ProjectionTuple index expr' typ

-- if expression is a record
evaluate e@(Record records)
    -- push blames to the top level
    | any isBlame $ exprs =
        let    blames = filter isBlame exprs
        in head blames
    -- push errors to the top level
    | any isError $ exprs =
        let    errors = filter isError exprs
        in head errors
    -- reduce expressions
    | any (not . isValue) exprs =
        let    exprs' = map evaluate exprs
        in Record $ zip labels exprs'
    | otherwise = e
    where (labels, exprs) = fromRecords records

-- if expression is a projection from records
evaluate e@(ProjectionRecord label expr typ)
    -- push blames to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr
    | not $ isValue expr =
        let v = evaluate expr
        in evaluationStyle $ ProjectionRecord label v typ
    -- project element of record
    | isRecord expr =
        let
            Record list = expr
            Just expr' = lookup label list
        in evaluationStyle expr'
    -- C-ProjectionRecord - simulate casts on data types
    | isCast expr =
        let
            (Cast t1 t2 expr') = expr
            -- get types from record
            RecordType list1 = t1
            RecordType list2 = t2
            t' = fromJust $ lookup label list1
            t'' = fromJust $ lookup label list2
        in evaluationStyle $ Cast t' t'' $ ProjectionRecord label expr' typ

-- if expression is a case
evaluate e@(Case expr (var1, expr1) (var2, expr2))
    -- push blames to top level
    | isBlame expr = expr
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr = expr
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr
    | not $ isValue expr =
        let v = evaluate expr
        in evaluationStyle $ Case v (var1, expr1) (var2, expr2)
    -- if is left tag
    | isLeftTag expr =
        let (LeftTag exprl typ) = expr
        in evaluationStyle $ substitute (var1, exprl) expr1
    -- if is right tag
    | isRightTag expr =
        let (RightTag exprr typ) = expr
        in evaluationStyle $ substitute (var2, exprr) expr2
    -- C-Case - simulate casts on data types
    | isCast expr =
        let
            (Cast t1 t2 expr') = expr
            (SumType t11 t12) = t1
            (SumType t21 t22) = t2
            cast1 = substitute (var1, Cast t11 t21 $ Variable var1) expr1
            cast2 = substitute (var2, Cast t12 t22 $ Variable var2) expr2
        in evaluationStyle $ Case expr' (var1, cast1) (var2, cast2)

-- if expression is a right tag
evaluate e@(LeftTag expr typ)
    -- push blames to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr
    | not $ isValue expr =
        let v = evaluate expr
        in LeftTag v typ
    | otherwise = e

-- if expression is a right tag
evaluate e@(RightTag expr typ)
    -- push blames to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr
    | not $ isValue expr =
        let v = evaluate expr
        in RightTag v typ
    | otherwise = e

-- if expression is a variant case
evaluate e@(CaseVariant expr alternatives)
    -- push blames to top level
    | isBlame expr = expr
    | any isBlame $ trd3 $ fromAlternatives alternatives = let
        blames = filter isBlame (trd3 $ fromAlternatives alternatives)
        in head blames
    -- push errors to top level
    | isError expr = expr
    | any isError $ trd3 $ fromAlternatives alternatives = let
        errors = filter isError (trd3 $ fromAlternatives alternatives)
        in head errors
    -- reduce expr
    | not $ isValue expr =
        let v = evaluate expr
        in evaluationStyle $ CaseVariant v alternatives
    -- if is tag
    | isTag expr =
        let
            (Tag label expr' _) = expr
            -- obtain correct alternative according to label
            (_, var, alternative) =
                head $ filter (\x -> label == (fst3 x)) alternatives
        in evaluationStyle $ substitute (var, expr') alternative
    -- C-CaseVariant - simulate casts on data types
    | isCast expr =
        let
            (Cast t1 t2 expr') = expr
            -- get types from variant
            list = zip (snd $ fromVariantType t1) (snd $ fromVariantType t2)
            -- build list with types from each alternative
            list' = zip list alternatives
            -- insert casts in each alternative
            casts = map
                (\x -> let
                    -- get types
                    t' = fst $ fst x
                    t'' = snd $ fst x
                    -- get label, var and expr
                    label = fst3 $ snd x
                    var = snd3 $ snd x
                    expr'' = trd3 $ snd x
                    cast = Cast t' t'' $ Variable var
                    in (label, var, substitute (var, cast) expr''))
                list'
        in evaluationStyle $ CaseVariant expr' casts

-- if expression is a tag
evaluate e@(Tag label expr typ)
    -- push blames to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr
    | not $ isValue expr =
        let v = evaluate expr
        in Tag label v typ
    | otherwise = e

-- if expression is a empty list
evaluate e@(Nil _) = e

-- if expression is a list constructor
evaluate e@(Cons t expr1 expr2)
    -- push blames to top level
    | isBlame expr1 = expr1
    | isBlame expr2 = expr2
    -- push errors to top level
    | isError expr1 = expr1
    | isError expr2 = expr2
    -- reduce expr1
    | not $ isValue expr1 =
        let v1 = evaluate expr1
        in evaluationStyle $ Cons t v1 expr2
    -- reduce expr2
    | not $ isValue expr2 =
        let v2 = evaluate expr2
        in evaluationStyle $ Cons t expr1 v2
    | otherwise = e

-- if expression is a test for empty list
evaluate e@(IsNil t expr)
    -- push blames to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr1
    | not $ isValue expr =
        let v = evaluate expr
        in evaluationStyle $ IsNil t v
    -- if is nil
    | isNil expr = evaluationStyle (Bool True)
    -- if is cons
    | isCons expr = evaluationStyle (Bool False)
    -- C-IsNil - simulate casts on data types
    | isCast expr =
        let    (Cast (ListType t1) (ListType t2) expr') = expr
        in evaluationStyle $ IsNil t1 expr'

-- if expression is a head of a list
evaluate e@(Head t expr)
    -- push blames to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr1
    | not $ isValue expr =
        let v = evaluate expr
        in evaluationStyle $ Head t v
    -- is nil
    | isNil expr = evaluationStyle $ Error "*** Exception: empty list"
    -- is cons
    | isCons expr =
        let (Cons t' expr1 expr2) = expr
        in evaluationStyle $ expr1
    -- C-Head - simulate casts on datatypes
    | isCast expr =
        let (Cast (ListType t1) (ListType t2) expr') = expr
        in evaluationStyle $ Cast t1 t2 $ Head t1 expr'

-- if expression is a tail of a list
evaluate e@(Tail t expr)
    -- push blames to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr1
    | not $ isValue expr =
        let v = evaluate expr
        in evaluationStyle $ Tail t v
    -- is nil
    | isNil expr = evaluationStyle $ Error "*** Exception: empty list"
    -- is cons
    | isCons expr =
        let (Cons t' expr1 expr2) = expr
        in evaluationStyle $ expr2
    -- C-Tail - simulate casts on datatypes
    | isCast expr =
        let (Cast (ListType t1) (ListType t2) expr') = expr
        in evaluationStyle $ Cast (ListType t1) (ListType t2) $ Tail t1 expr'

-- if expression is a fold
evaluate e@(Fold typ expr)
    -- push blame to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr
    | not $ isValue expr =
        let v = evaluate expr
        in Fold typ v
    | otherwise = e

-- if expression is a fold
evaluate e@(Unfold typ expr)
    -- push blame to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- reduce expr
    | not $ isValue expr =
        let v = evaluate expr
        in Unfold typ v
    -- if expression is an unfold of a fold
    | isFold expr =
        let (Fold _ expr') = expr
        in expr'
    -- C-Unfold - simulate casts on data types
    | isCast expr =
        let
            (Cast t1 t2 expr') = expr
            (Mu var1 t1') = t1
            (Mu var2 t2') = t2
            t1'' = unfoldType (var1, t1) t1'
            t2'' = unfoldType (var2, t2) t2'
            cast = Cast t1'' t2'' $ Unfold typ expr'
            in evaluationStyle cast

-- if expression is a type information
evaluate e@(TypeInformation typ expr) = expr

-- if expression is a cast
evaluate e@(Cast t1 t2 expr)
    -- push blame to top level
    | isBlame expr = expr
    -- push errors to top level
    | isError expr = expr
    -- values don't reduce
    | isValue e = e
    -- evaluate inside a cast
    | (not $ isValue expr) =
        let expr2 = evaluate expr
        in evaluationStyle $ Cast t1 t2 expr2
    -- ID-BASE - remove casts to same types
    | isValue expr && t1 == t2 = evaluationStyle expr
    -- SUCCEED - cast is sucessful
    | isCast expr && t1 == DynType && t2' == DynType &&    isGroundType t2 && t1' == t2 =
            evaluationStyle expr'
    -- FAIL - cast fails
    | isCast expr && t1 == DynType && t2' == DynType &&
        isGroundType t2 && isGroundType t1' && (not $ sameGround t1' t2) =
            Blame t2 $ "cannot cast from " ++ (show t1') ++ " to " ++ (show t2)
    -- GROUND - cast types through their ground types
    | (not $ isGroundType t1) && t2 == DynType =
        let g = getGroundType t1
        in evaluationStyle $ Cast g DynType $ Cast t1 g expr
    -- EXPAND - cast types through their ground types
    | (not $ isGroundType t2) && t1 == DynType =
        let g = getGroundType t2
        in evaluationStyle $ Cast g t2 $ Cast DynType g expr
    -- Project types and expression from inner casts
    where (Cast t1' t2' expr') = expr

-- blames are values
evaluate e@(Blame _ _) = e

-- errors are values
evaluate e@(Error _) = e

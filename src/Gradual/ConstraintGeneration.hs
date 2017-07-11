module Gradual.ConstraintGeneration (
    generateConstraints
) where

-- Syntax & Types
import Gradual.Syntax
import Gradual.Types

-- Imports
import Control.Monad.State
import Control.Monad.Except
import Data.Maybe

-- generate constraint set and type given a context and expression
generateConstraints :: (Context, Expression)
    -> StateT Int (Except String) (Type, Constraints, Expression)

-- (Cx) if expression is a variable
generateConstraints (ctx, Variable var) = do
    -- obtain type from context
    let varType = lookup var ctx
    -- check if variable exists in context
    if isNothing varType then
        -- if not, throw error
        throwError $ "Error: Variable " ++ var ++ " does not exist!! Terms must be closed!!"
    else do
        -- retrieve type
        let (finalType, constraints) = fromJust $ varType
        i <- get
        -- replace quantified variables by type variables
        -- instantiation of Damas-Milner
        let ((finalType', constraints'), i') =
                runState (replaceQuantifiedVariables finalType constraints) i
        put (i')
        -- build typed expression
        let typedExpr = TypeInformation finalType' (Variable var)
        -- return type
        return (finalType', constraints', typedExpr)

-- (Cλ) if expression is a abstraction
generateConstraints (ctx, Abstraction var expr) = do
    -- counter for variable creation
    i <- get
    put (i+1)
    -- create new type variable
    let newVar1 = newTypeVar i
    -- create a binding between the abstraction variable and the new type variable
    let binding = (var, (ForAll "" newVar1, []))
    -- build type assignment with new binding
    let typeAssignment = (binding : ctx, expr)
    -- obtain type and generate constraints for new type assignment
    (exprType, constraints, expr_typed) <- generateConstraints typeAssignment
    -- build typed expression
    let typedExpr = TypeInformation (ArrowType newVar1 exprType) (Abstraction var expr_typed)
    -- return arrow type and constraints
    return (ArrowType newVar1 exprType, constraints, typedExpr)

-- (Capp) if expression is a application
generateConstraints (ctx, Application expr1 expr2) = do
    -- build for each expression in the application
    -- a type assignment
    let typeAssignment1 = (ctx, expr1)
    let typeAssignment2 = (ctx, expr2)
    -- obtain type and constraints for both expressions
    (t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
    (t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
    -- get constraints for codomain and domain relation
    (t3, constraints3) <- codomain t1
    constraints4 <- domain t1 t2
    -- build typed expression
    let typedExpr = TypeInformation t3 (Application expr1_typed expr2_typed)
    -- return type along with all the constraints
    return (t3, constraints1 ++ constraints2 ++ constraints3 ++ constraints4, typedExpr)

-- (C::) if expression is an ascription
generateConstraints (ctx, Ascription expr typ) = do
    -- build type assignment for expression
    let typeAssignment = (ctx, expr)
    -- obtain type and generate constraints for type assignment
    (exprType, constraints, expr_typed) <- generateConstraints typeAssignment
    -- build typed expression
    let typedExpr = TypeInformation typ (Ascription expr_typed typ)
    -- return type along with all the constraints
    return (typ, constraints ++ [Consistency exprType typ], typedExpr)

-- (Cλ:) if expression is a annotated abstraction
generateConstraints (ctx, Annotation var typ expr) = do
    -- create a binding between the abstraction variable and the annotated type
    let binding = (var, (ForAll "" typ, []))
    -- build type assignment with new binding
    let typeAssignment = (binding : ctx, expr)
    -- obtain type and generate constraints for new type assignment
    (exprType, constraints, expr_typed) <- generateConstraints typeAssignment
    -- build typed expression
    let typedExpr = TypeInformation (ArrowType typ exprType) (Annotation var typ expr_typed)
    -- return arrow type and constraints
    return (ArrowType typ exprType, constraints, typedExpr)

-- (Cn) if expression is a integer
generateConstraints (ctx, Int int) = do
    -- build typed expression
    let typedExpr = TypeInformation IntType (Int int)
    -- return Int type
    return (IntType, [], typedExpr)

-- (Cb) if expression is a boolean
generateConstraints (ctx, Bool bool) = do
    -- build typed expression
    let typedExpr = TypeInformation BoolType (Bool bool)
    -- return Bool type
    return (BoolType, [], typedExpr)

-- (Clet) if expression is a let binding
generateConstraints (ctx, Let var expr1 expr2)
    -- (Cletp) if expression is a let binding a value to a variable
    | isValue expr1 || isAnnotation expr1 = do
        -- build type assignment for value
        let typeAssignment1 = (ctx, expr1)
        -- obtain type and generate constraints for type assignment
        (t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
        -- generalize type variables
        let t1' = generalizeTypeVariables ctx t1
        -- build type assignment for value
        let typeAssignment2 = ((var, (t1', constraints1)) : ctx, expr2)
        -- obtain type and generate constraints for type assignment
        (t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
        -- build typed expression
        let typedExpr = TypeInformation t2 (Let var expr1_typed expr2_typed)
        -- return type along with all the constraints
        return (t2, constraints1 ++ constraints2, typedExpr)
    -- (Clet) if expression is a let binding a expression to a variable
    | otherwise = do
        -- build type assignment for value
        --let typeAssignment1 = (ctx, expr1)
        -- obtain type and generate constraints for type assignment
        --(t1, _, expr1_typed) <- generateConstraints typeAssignment1
        -- generalize type variables
        --let t1' = generalizeTypeVariables t1
        -- build type assignment for value
        --let typeAssignment2 = ((var, t1') : ctx, expr2)
        -- obtain type and generate constraints for type assignment
        --(_, _, expr2_typed) <- generateConstraints typeAssignment2
        -- build type assignment for expression
        let typeAssignment = (ctx, Application (Abstraction var expr2) expr1)
        -- obtain type and generate constraints for type assignment
        (t, constraints, expr_typed) <- generateConstraints typeAssignment
        -- build typed expression
        --let typedExpr = TypeInformation t (Let var expr1_typed expr2_typed)
        -- return type along with all the constraints
        return (t, constraints, expr_typed)

-- (Cfix) if expression is a fixed point
generateConstraints (ctx, Fix expr) = do
    -- build type assignment
    let typeAssignment1 = (ctx, expr)
    -- obtain type and generate constraints for type assignment
    (t, constraints1, expr_typed) <- generateConstraints typeAssignment1
    (ArrowType t1 t2, constraints2) <- patternMatchArrow t
    -- build typed expression
    let typedExpr = TypeInformation t1 (Fix expr_typed)
    return (t1, constraints1 ++ constraints2 ++ [Consistency t1 t2], typedExpr)

-- (Cletrec) if expression is a recursive let binding
generateConstraints (ctx, LetRec var expr1 expr2) = do
    -- build type assignment
    let typeAssignment = (ctx, Let var (Fix $ Abstraction var expr1) expr2)
    -- obtain type and generate constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    -- build type assignment
    --let typeAssignment1 = (ctx, expr1)
    -- obtain type and generate constraints for type assignment
    --(t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
    -- generalize type variables
    --let t1' = generalizeTypeVariables t1
    -- build type assignment
    --let typeAssignment2 = ((var, t1') : ctx, expr2)
    -- obtain type and generate constraints for type assignment
    --(_, constraints2, expr2_typed) <- generateConstraints typeAssignment2
    -- build typed expression
    --let typedExpr = TypeInformation t (LetRec var expr1_typed expr2_typed)
    return (t, constraints, expr_typed)

-- (Cif) if expression if a conditional statement
generateConstraints (ctx, If expr1 expr2 expr3) = do
    -- build for each expression in the application a type assignment
    let typeAssignment1 = (ctx, expr1)
    let typeAssignment2 = (ctx, expr2)
    let typeAssignment3 = (ctx, expr3)
    -- obtain type and constraints for all the expressions
    (t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
    (t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
    (t3, constraints3, expr3_typed) <- generateConstraints typeAssignment3
    (t4, constraints4) <- lift $ meet t2 t3
    -- build typed expression
    let typedExpr = TypeInformation t4 (If expr1_typed expr2_typed expr3_typed)
    -- return type along with all the constraints
    return (t4, constraints1 ++ constraints2
        ++ constraints3 ++ constraints4 ++ [Consistency t1 BoolType], typedExpr)

-- if expression is an arithmetic or relational operator
generateConstraints (ctx, expr)
    -- if expression is an addition (C+), subtraction (C-),
    -- multiplication (C*), or division (C/)
    | isArithmeticOperator expr = do
        -- build for each expression in the addition a type assignment
        let typeAssignment1 = (ctx, expr1)
        let typeAssignment2 = (ctx, expr2)
        -- obtain type and constraints for both expressions
        (t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
        (t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
        -- build typed expression
        let expr_typed
                | isAddition expr = Addition expr1_typed expr2_typed
                | isSubtraction expr = Subtraction expr1_typed expr2_typed
                | isMultiplication expr = Multiplication expr1_typed expr2_typed
                | isDivision expr = Division expr1_typed expr2_typed
        -- insert type information
        let typedExpr = TypeInformation IntType expr_typed
        -- return type along with all the constraints
        return (IntType, constraints1 ++ constraints2 ++
            [Consistency t1 IntType, Consistency t2 IntType], typedExpr)
    -- if expression is an equality (C==), not equality (C/=), lesser than (C<),
    -- greater than (C>), lesser than or equal to (C<=) or greater than or equal to (C>=) check
    | isRelationalOperator expr = do
        -- build for each expression in the addition a type assignment
        let typeAssignment1 = (ctx, expr1)
        let typeAssignment2 = (ctx, expr2)
        -- obtain type and constraints for both expressions
        (t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
        (t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
        -- build typed expression
        let expr_typed
                | isEqual expr = Equal expr1_typed expr2_typed
                | isNotEqual expr = NotEqual expr1_typed expr2_typed
                | isLessThan expr = LesserThan expr1_typed expr2_typed
                | isGreaterThan expr = GreaterThan expr1_typed expr2_typed
                | isLessEqualTo expr = LesserEqualTo expr1_typed expr2_typed
                | isGreaterEqualTo expr = GreaterEqualTo expr1_typed expr2_typed
        -- insert type information
        let typedExpr = TypeInformation BoolType expr_typed
        -- return type along with all the constraints
        return (BoolType, constraints1 ++ constraints2 ++
            [Consistency t1 IntType, Consistency t2 IntType], typedExpr)
    -- retrieve sub expressions from the operator
    where (expr1, expr2) = fromOperator expr

-- (Cunit) if expression is an unit
generateConstraints (ctx, Unit) = do
    -- return type along with all the constraints
    return (UnitType, [], TypeInformation UnitType Unit)

-- (Cpair) if expression is a pair
generateConstraints (ctx, Pair expr1 expr2) = do
    -- build for each expression a type assignment
    let typeAssignment1 = (ctx, expr1)
    let typeAssignment2 = (ctx, expr2)
    -- obtain type and constraints for both expressions
    (t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
    (t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
    -- build typed expression
    let typedExpr = TypeInformation (ProductType t1 t2) (Pair expr1_typed expr2_typed)
    -- return type along with all the constraints
    return (ProductType t1 t2, constraints1 ++ constraints2, typedExpr)

-- (Cfst) if expression is a first projection
generateConstraints (ctx, First expr) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints1, expr_typed) <- generateConstraints typeAssignment
    (ProductType t1 t2, constraints2) <- patternMatchProduct t
    -- build typed expression
    let typedExpr = TypeInformation t1 (First expr_typed)
    -- return type along with all the constraints
    return (t1, constraints1 ++ constraints2, typedExpr)

-- (Csnd) if expression is a second projection
generateConstraints (ctx, Second expr) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints1, expr_typed) <- generateConstraints typeAssignment
    (ProductType t1 t2, constraints2) <- patternMatchProduct t
    -- build typed expression
    let typedExpr = TypeInformation t2 (Second expr_typed)
    -- return type along with all the constraints
    return (t2, constraints1 ++ constraints2, typedExpr)

-- (Ctuple) if expression is a tuple
generateConstraints (ctx, Tuple exprs) = do
    -- build for each expression a type assignment
    let typeAssignments = map (\x -> (ctx, x)) exprs
    -- obtain type and constraints for the expressions
    results <- mapM generateConstraints typeAssignments
    -- get resulting types and constraints
    let (types, cs, exprs_typed) = unzip3 results
    -- build typed expression
    let typedExpr = TypeInformation (TupleType types) (Tuple exprs_typed)
    -- return type along with all the constraints
    return (TupleType types, concat cs, typedExpr)

-- (Cprojectiontuple) if expression is a projection from tuples
generateConstraints (ctx, ProjectionTuple index expr typ) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    -- if expression is annotated with a tuple type
    if isTupleType typ then do
        -- retrieve type
        let TupleType types = typ
        -- if tuple is smaller than projection index
        if length types <= index then do
            -- build typed expression
            let typedExpr = TypeInformation UnitType (ProjectionTuple index expr_typed typ)
            let cs = [Equality typ (TupleType [UnitType])]
            return (UnitType, constraints ++ cs, typedExpr)
        else do
            let size = length types
            -- get constraints for each type in tuple
            (TupleType list, constraints') <- patternMatchTuple size t
            -- let type of expr according to the index
            let finalType = list !! index
            -- build typed expression
            let typedExpr = TypeInformation finalType (ProjectionTuple index expr_typed typ)
            -- return type along with all the constraints
            return (finalType, constraints ++ constraints' ++
                [Consistency (TupleType list) typ], typedExpr)
    -- if expression is annotated with a wrong type
    else do
        -- build typed expression
        let typedExpr = TypeInformation UnitType (ProjectionTuple index expr_typed typ)
        let typ' = TupleType [UnitType]
        return (UnitType, constraints ++ [Equality typ typ'], typedExpr)

-- (Crecord) if expression is a record
generateConstraints (ctx, Record records) = do
    -- get labels and types
    let (labels, exprs) = fromRecords records
    -- build for each expression a type assignment
    let typeAssignments = map (\x -> (ctx, x)) exprs
    -- obtain type and constraints for both expressions
    results <- mapM generateConstraints typeAssignments
    -- get resulting types and constraints
    let (types, cs, exprs_typed) = unzip3 results
    -- build type
    let ts = zip labels types
    -- build typed expression
    let typedExpr = TypeInformation (RecordType ts) (Record $ zip labels exprs_typed)
    -- return type along with all the constraints
    return (RecordType ts, concat cs, typedExpr)

-- (Cprojectionrecords) if expression is a projection from records
generateConstraints (ctx, ProjectionRecord label expr typ) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    -- if expression is annotated with a record type
    if isRecordType typ then do
        -- retrieve type
        let RecordType records = typ
        -- obtain type according to tag
        let tagType = lookup label records
        -- if type doesn't exist in record
        if isNothing tagType then do
            -- build typed expression
            let typedExpr = TypeInformation UnitType (ProjectionRecord label expr_typed typ)
            let cs = [Equality typ (RecordType [(label, UnitType)])]
            return (UnitType, constraints ++ cs, typedExpr)
        else do
            -- get labels
            let (labels, _) = fromRecordType typ
            -- get constraints for each type in record
            (RecordType list, constraints') <- patternMatchRecord labels t
            -- let type of expr be a type variable according to the label
            let finalType = fromJust $ lookup label list
            -- build typed expression
            let typedExpr = TypeInformation finalType (ProjectionRecord label expr_typed typ)
            -- return type along with all the constraints
            return (finalType, constraints ++ constraints' ++
                [Consistency (RecordType list) typ], typedExpr)
    -- if expression is annotated with a wrong type
    else do
        -- build typed expression
        let typedExpr = TypeInformation UnitType (ProjectionRecord label expr_typed typ)
        let typ' = RecordType [(label, UnitType)]
        return (UnitType, constraints ++ [Equality typ typ'], typedExpr)

-- (Ccase) if expression is a case
generateConstraints (ctx, Case expr (var1, expr1) (var2, expr2)) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    (SumType t1' t2', constraints') <- patternMatchSum t
    -- build for each expression in the application a type assignment
    let typeAssignment1 = ((var1, (t1',[])) : ctx, expr1)
    let typeAssignment2 = ((var2, (t2',[])) : ctx, expr2)
    -- obtain type and constraints for both expressions
    (t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
    (t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
    (t3, constraints3) <- lift $ meet t1 t2
    -- build typed expression
    let typedExpr = TypeInformation t3 (Case expr_typed (var1, expr1_typed) (var2, expr2_typed))
    -- return type along with all the constraints
    return (t3, constraints ++ constraints' ++
        constraints1 ++ constraints2 ++ constraints3, typedExpr)

-- (Cinl) if expression is a left tag
generateConstraints (ctx, LeftTag expr typ) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    (SumType t1 _, constraints2) <- patternMatchSum typ
    -- build typed expression
    let typedExpr = TypeInformation typ $ LeftTag expr_typed typ
    -- return type along with all the constraints
    return (typ, constraints ++ constraints2 ++ [Consistency t t1], typedExpr)

-- (Cinr) if expression is a right tag
generateConstraints (ctx, RightTag expr typ) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    (SumType _ t2, constraints2) <- patternMatchSum typ
    -- build typed expression
    let typedExpr = TypeInformation typ $ RightTag expr_typed typ
    -- return type along with all the constraints
    return (typ, constraints ++ [Consistency t t2], typedExpr)

-- (Ccasevariant) if expression is a variant case
generateConstraints (ctx, CaseVariant expr alternatives) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    -- get constraints for each type in variant
    (VariantType list, constraints') <-
        patternMatchVariant (fst3 $ fromAlternatives alternatives) t
    let (_, types) = unzip list
    -- build for each expression a type assignment
    let typeAssignments = map
            (\x -> let
                -- get type variable from alternative
                var = snd3 $ snd x
                -- get expression from alternative
                expr' = trd3 $ snd x
                -- get type from types
                typ = fst x
                -- add to context variable with new type
                in ((var, (typ, [])) : ctx, expr'))
            $ zip types alternatives
    -- obtain type and constraints for expressions
    results <- mapM generateConstraints typeAssignments
    -- get resulting types, constraints and typed expressions
    let (ts, cs, exprs_typed) = unzip3 results
    (t3, constraints'') <- lift $ foldM meetM (head ts, []) (tail ts)
    -- build each typed expression
    let typedAlternatives = map
            (\x -> let
                -- get label
                label = fst3 $ fst x
                -- get var
                var = snd3 $ fst x
                -- get typed expression
                expr_typed = snd x
                in (label, var, expr_typed))
            $ zip alternatives exprs_typed
    -- build typed expression
    let typedExpr = TypeInformation t3 (CaseVariant expr_typed typedAlternatives)
    -- return type along with all the constraints
    return (t3, constraints ++ (concat cs) ++
        constraints' ++ constraints'', typedExpr)

-- (Ctag) if expression is a tag
generateConstraints (ctx, Tag label expr typ) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    -- if expression is annotated with a variant type
    if isVariantType typ then do
        -- retrieve type
        let VariantType list = typ
        -- obtain type according to tag
        let tagType = lookup label list
        -- if type doesn't exist in variant
        if isNothing tagType then do
            -- build typed expression
            let typedExpr = TypeInformation typ (Tag label expr_typed typ)
            let cs = [Equality typ (VariantType [(label, t)])]
            return (typ, constraints ++ cs, typedExpr)
        else do
            -- build typed expression
            let typedExpr = TypeInformation typ (Tag label expr_typed typ)
            -- return type along with all the constraints
            return (typ, constraints ++
                [Consistency (fromJust tagType) t], typedExpr)
    -- if expression is annotated with other than variant type
    else do
        let typ' = VariantType [(label, t)]
        -- build typed expression
        let typedExpr = TypeInformation typ' (Tag label expr_typed typ)
        return (typ', constraints ++ [Consistency typ typ'], typedExpr)

-- (Cnil) if expression is an empty list
generateConstraints (ctx, Nil typ) = do
    -- return type along with all the constraints
    return (ListType typ, [], TypeInformation (ListType typ) $ Nil typ)

-- (Ccons) if expression is a list constructor
generateConstraints (ctx, Cons typ expr1 expr2) = do
    -- build for each expression a type assignment
    let typeAssignment1 = (ctx, expr1)
    let typeAssignment2 = (ctx, expr2)
    -- obtain type and constraints for both expressions
    (t1, constraints1, expr1_typed) <- generateConstraints typeAssignment1
    (t2, constraints2, expr2_typed) <- generateConstraints typeAssignment2
    (ListType t', constraints3) <- patternMatchList t2
    -- build typed expression
    let typedExpr = TypeInformation (ListType typ) (Cons typ expr1_typed expr2_typed)
    -- return type along with all the constraints
    return (ListType typ, constraints1 ++ constraints2 ++ constraints3 ++
        [Consistency t1 typ, Consistency t' typ], typedExpr)

-- (Cisnil) if expression is a test for empty list
generateConstraints (ctx, IsNil typ expr) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    (ListType t', constraints') <- patternMatchList t
    -- build typed expression
    let typedExpr = TypeInformation BoolType (IsNil typ expr_typed)
    -- return type along with all the constraints
    return (BoolType, constraints ++ constraints' ++ [Consistency t' typ], typedExpr)

-- (Chead) if expression is the head of a list
generateConstraints (ctx, Head typ expr) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    (ListType t', constraints') <- patternMatchList t
    -- build typed expression
    let typedExpr = TypeInformation typ (Head typ expr_typed)
    -- return type along with all the constraints
    return (typ, constraints ++ constraints' ++ [Consistency t' typ], typedExpr)

-- (Ctail) if expression is the tail of a list
generateConstraints (ctx, Tail typ expr) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    (ListType t', constraints') <- patternMatchList t
    -- build typed expression
    let typedExpr = TypeInformation (ListType typ) (Tail typ expr_typed)
    -- return type along with all the constraints
    return (ListType typ, constraints ++ constraints' ++ [Consistency t' typ], typedExpr)

-- (Cfold) if expression is a fold
generateConstraints (ctx, Fold typ expr) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    -- unfold type
    let (Mu var typ') = typ
    let t' = unfoldType (var, typ) typ'
    -- build typed expression
    let typedExpr = TypeInformation typ (Fold typ expr_typed)
    -- return type along with all the constraints
    return (typ, constraints ++ [Consistency t' t], typedExpr)

-- (Cunfold) if expression is a unfold
generateConstraints (ctx, Unfold typ expr) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    let (Mu var typ'') = typ
    (Mu var' typ', constraints2) <- patternMatchMu var t
    -- unfold type
    let unfoldedType = unfoldType (var, Mu var typ'') typ''
    -- build typed expression
    let typedExpr = TypeInformation unfoldedType (Unfold typ expr_typed)
    -- return type along with all the constraints
    return (unfoldedType, constraints ++ constraints2 ++
        [Consistency typ (Mu var' typ')], typedExpr)

{-
-- (Cunfold) if expression is a unfold
generateConstraints (ctx, Unfold typ expr) = do
    -- counter for variable creation
    i <- get
    put (i+1)
    -- create new type variable
    let newVar1 = newTypeVar i
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints, expr_typed) <- generateConstraints typeAssignment
    -- unfold type
    let (Mu var typ') = typ
    let t' = unfoldType (var, typ) typ'
    -- build typed expression
    let typedExpr = TypeInformation t' (Unfold typ expr_typed)
    -- return type along with all the constraints
    return (t', constraints ++ [Consistency typ t], typedExpr)
-}

-- (C:) if expression if a type information
generateConstraints (ctx, e@(TypeInformation typ expr)) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and generate constraints for type assignment
    (t, constraints, _) <- generateConstraints typeAssignment
    -- return type along with all the constraints
    return (t, constraints, e)

-- (Cerr) if expression if an error
generateConstraints (ctx, e@(Error msg)) = do
    -- counter for variable creation
    i <- get
    put (i+1)
    -- create new type variable
    let newVar1 = newTypeVar i
    -- build typed expression
    let typedExpr = TypeInformation newVar1 (Error msg)
    -- return type along with all the constraints
    return (newVar1, [], typedExpr)

-- Replace types bound by for all quantifiers with fresh variables
replaceQuantifiedVariables :: Type -> Constraints -> State Int (Type, Constraints)
replaceQuantifiedVariables typ constraints = do
    -- collect bound type
    let vars = collectBoundTypes typ
    let lengthVars = length vars
    -- counter for variables creation
    i <- get
    put (i + lengthVars)
    -- generate lists of new types vriables
    let newVars = map newTypeVar [i..i+lengthVars-1]
    --- generate substitutions
    let substitutions = map (\x -> (VarType $ fst x, snd x)) $ zip vars newVars
    -- apply substitutions to type and constraints
    let typ' = foldr substituteType (removeQuantifiers typ) substitutions
    let constraints' = map (\x -> foldr substituteConstraint x substitutions) constraints
    return (typ', constraints')

-- generate constraints and type for codomain relation
codomain :: Type -> StateT Int (Except String) (Type, Constraints)
codomain t
    -- if t is type variable
    | isVarType t = do
        -- create two new type variables t1 and t2
        i <- get
        put (i+2)
        let t1 = newTypeVar i
        let t2 = newTypeVar (i+1)
        -- return as type t2 and equality constraint t =C t1 -> t2
        return (t2, [Equality t (ArrowType t1 t2)])
    -- if t is arrow type
    | isArrowType t = do
        -- let t1 and t2 such that t =C t1 -> t2
        let (ArrowType t1 t2) = t
        -- return as type t2
        return (t2, [])
    -- if t is dynamic type
    | isDynType t = do
        -- return dynamic typ
        return (DynType, [])
    -- throw error
    | otherwise = throwError $ "Error: Type " ++ (show t) ++ " has no codomain!!"

-- generate constraints for domain relation
domain :: Type -> Type -> StateT Int (Except String) Constraints
domain t1 t2
    -- if t1 is type variable
    | isVarType t1 = do
        -- create two new type variables t11 and t12
        i <- get
        put (i+2)
        let t11 = newTypeVar i
        let t12 = newTypeVar (i+1)
        -- return constraints t11 ~C t2 and t1 =C t11 -> t12
        return [Consistency t11 t2, Equality t1 (ArrowType t11 t12)]
    -- if t1 is arrow type
    | isArrowType t1 = do
        -- let t11 and t12 such that t1 =C t11 -> t12
        let (ArrowType t11 t12) = t1
        -- return constraints t11 ~C t2
        return [Consistency t11 t2]
    -- if t1 is dynamic type
    | isDynType t1 = do
        -- return constraints ? ~C t2
        return [Consistency DynType t2]
    -- throw error
    | otherwise = throwError $ "Error: Type " ++ (show t1) ++ " has no domain!!"

-- generate components of arrow type
patternMatchArrow :: Type -> StateT Int (Except String) (Type, Constraints)
patternMatchArrow t
    -- if t is type variable
    | isVarType t = do
        -- create two new type variables t11 and t12
        i <- get
        put (i+2)
        let t1 = newTypeVar i
        let t2 = newTypeVar (i+1)
        -- return constraints t1 =C t11 -> t12
        return (ArrowType t1 t2, [Equality t (ArrowType t1 t2)])
    -- if t1 is arrow type
    | isArrowType t = do
        -- let t1 and t2 such that t =C t1 -> t2
        let (ArrowType t1 t2) = t
        -- return constraints t11 ~C t2
        return (t, [])
    -- if t1 is dynamic type
    | isDynType t = do
        -- return constraints ? ~C t2
        return (ArrowType DynType DynType, [])
    -- throw error
    | otherwise = throwError $ "Error: Type " ++ (show t) ++ " in not an arrow type!!"

-- generate constraints and type for meet relation
meet :: Type -> Type -> Except String (Type, Constraints)
meet t1 t2
    | isIntType t1 && isIntType t2 = return (IntType, [])
    | isBoolType t1 && isBoolType t2 = return (BoolType, [])
    | isUnitType t1 && isUnitType t2 = return (UnitType, [])
    | isDynType t2 = return (t1, [Consistency t1 DynType])
    | isDynType t1 = return (t2, [Consistency DynType t2])
    | isVarType t1 = return (t1, [Consistency t1 t2])
    | (not $ isVarType t1) && isVarType t2 = return (t2, [Consistency t1 t2])
    | isArrowType t1 && isArrowType t2 = do
        let    (ArrowType t11 t12) = t1
        let (ArrowType t21 t22) = t2
        (t1', constraints1) <- meet t11 t21
        (t2', constraints2) <- meet t12 t22
        return (ArrowType t1' t2', constraints1 ++ constraints2)
    | isProductType t1 && isProductType t2 = do
        let    (ProductType t11 t12) = t1
        let (ProductType t21 t22) = t2
        (t1', constraints1) <- meet t11 t21
        (t2', constraints2) <- meet t12 t22
        return (ProductType t1' t2', constraints1 ++ constraints2)
    | isTupleType t1 && isTupleType t2 && compareSize t1 t2 = do
        let TupleType types1 = t1
        let TupleType types2 = t2
        let list = zip types1 types2
        -- run meet for each pair of types
        results <- mapM (\x -> meet (fst x) (snd x)) list
        -- get resulting types
        let ts = map fst results
        -- get resulting constraints
        let cs = map snd results
        return (TupleType ts, concat cs)
    | isRecordType t1 && isRecordType t2 && compareLabels t1 t2 = do
        let (labels1, types1) = fromRecordType t1
        let (_, types2) = fromRecordType t2
        let list = zip types1 types2
        -- run meet for each pair of types
        results <- mapM (\x -> meet (fst x) (snd x)) list
        -- get resulting types
        let ts = map fst results
        -- get resulting constraints
        let cs = map snd results
        return (RecordType $ zip labels1 ts, concat cs)
    | isSumType t1 && isSumType t2 = do
        let    (SumType t11 t12) = t1
        let (SumType t21 t22) = t2
        (t1', constraints1) <- meet t11 t21
        (t2', constraints2) <- meet t12 t22
        return (SumType t1' t2', constraints1 ++ constraints2)
    | isVariantType t1 && isVariantType t2 && compareLabels t1 t2 = do
        let (labels1, types1) = fromVariantType t1
        let (_, types2) = fromVariantType t2
        let list = zip types1 types2
        -- run meet for each pair of types
        results <- mapM (\x -> meet (fst x) (snd x)) list
        -- get resulting types
        let ts = map fst results
        -- get resulting constraints
        let cs = map snd results
        return (VariantType $ zip labels1 ts, concat cs)
    | isListType t1 && isListType t2 = do
        let    (ListType t1') = t1
        let (ListType t2') = t2
        (t, constraints) <- meet t1' t2'
        return (ListType t, constraints)
    | isMuType t1 && isMuType t2 && compareVars t1 t2 = do
        let (Mu var1 t1') = t1
        let (Mu var2 t2') = t2
        (t, constraints) <- meet t1' t2'
        return (Mu var1 t, constraints)
    | otherwise = throwError $
        "Error: Types " ++ (show t1) ++ " and " ++ (show t2) ++ " are not compatible!!"

meetM :: (Type, Constraints) -> Type -> Except String (Type, Constraints)
meetM (t1, c) t2 = do
    (t, constraints) <- meet t1 t2
    return (t, c ++ constraints)

-- get components of sum type
patternMatchProduct :: Type -> StateT Int (Except String) (Type, Constraints)
patternMatchProduct t
    -- if t is type variable
    | isVarType t = do
        -- create two new type variables t1 and t2
        i <- get
        put (i+2)
        let t1 = newTypeVar i
        let t2 = newTypeVar (i+1)
        -- return types and equality relation t =C t1 × t2
        return (ProductType t1 t2, [Equality t (ProductType t1 t2)])
    -- if t is sum type
    | isProductType t = do
        -- return types
        return (t, [])
    -- if t is dynamic type
    | isDynType t = do
        -- return dynamic typ
        return (ProductType DynType DynType, [])
    -- throw error
    | otherwise =
        throwError $ "Error: Type " ++ (show t) ++ " is not a product type!!"

-- get components of tuple type
patternMatchTuple :: Int -> Type
    -> StateT Int (Except String) (Type, Constraints)
patternMatchTuple n t
    -- if t is type variable
    | isVarType t = do
        -- counter for variable creation
        i <- get
        put (i+n)
        -- create new type variables
        let typeVars = map newTypeVar [i..i+n-1]
        -- return types and equality relation t =C {Ti}
        return (TupleType typeVars, [Equality t (TupleType typeVars)])
    -- if t is tuple type
    | isTupleType t = do
        -- return types
        return (t, [])
    -- if t is dynamic type
    | isDynType t = do
        -- return dynamic type
        return (TupleType $ replicate n DynType, [])
    -- throw error
    | otherwise =
        throwError $ "Error: Type " ++ (show t) ++ " is not a tuple type!!"

-- get components of record type
patternMatchRecord :: [Label] -> Type
    -> StateT Int (Except String) (Type, Constraints)
patternMatchRecord labels t
    -- if t is type variable
    | isVarType t = do
        -- counter for variable creation
        i <- get
        put (i+n)
        -- create new type variables
        let typeVars = map newTypeVar [i..i+n-1]
        -- build type consisting of new type variables
        let list = zip labels typeVars
        -- return types and equality relation t =C {li:Ti}
        return (RecordType list, [Equality t (RecordType list)])
    -- if t is record type
    | isRecordType t = do
        -- return types
        return (t, [])
    -- if t is dynamic type
    | isDynType t = do
        -- return dynamic type
        return (RecordType $ zip labels $ replicate n DynType, [])
    -- throw error
    | otherwise =
        throwError $ "Error: Type " ++ (show t) ++ " is not a record type!!"
    -- number of fields
    where n = length labels

-- get components of sum type
patternMatchSum :: Type -> StateT Int (Except String) (Type, Constraints)
patternMatchSum t
    -- if t is type variable
    | isVarType t = do
        -- create two new type variables t1 and t2
        i <- get
        put (i+2)
        let t1 = newTypeVar i
        let t2 = newTypeVar (i+1)
        -- return types and equality relation t =C t1 + t2
        return (SumType t1 t2, [Equality t (SumType t1 t2)])
    -- if t is sum type
    | isSumType t = do
        -- return types
        return (t, [])
    -- if t is dynamic type
    | isDynType t = do
        -- return dynamic typ
        return (SumType DynType DynType, [])
    -- throw error
    | otherwise =
        throwError $ "Error: Type " ++ (show t) ++ " is not a sum type!!"

-- get components of variant type
patternMatchVariant :: [Label] -> Type
    -> StateT Int (Except String) (Type, Constraints)
patternMatchVariant labels t
    -- if t is type variable
    | isVarType t = do
        -- counter for variable creation
        i <- get
        put (i+n)
        -- create new type variables
        let typeVars = map newTypeVar [i..i+n-1]
        -- build type consisting of new type variables
        let list = zip labels typeVars
        -- return types and equality relation t =C <li:Ti>
        return (VariantType list, [Equality t (VariantType list)])
    -- if t is variant type
    | isVariantType t = do
        -- return types
        return (t, [])
    -- if t is dynamic type
    | isDynType t = do
        -- return dynamic type
        return (VariantType $ zip labels $ replicate n DynType, [])
    -- throw error
    | otherwise =
        throwError $ "Error: Type " ++ (show t) ++ " is not a variant type!!"
    -- number of alternatives
    where n = length labels

-- get components of list type
patternMatchList :: Type -> StateT Int (Except String) (Type, Constraints)
patternMatchList t
    -- if t is type variable
    | isVarType t = do
        -- create a new type variables t'
        i <- get
        put (i+1)
        let t' = newTypeVar i
        -- return types and equality relation t =C [t']
        return (ListType t', [Equality t (ListType t')])
    -- if t is sum type
    | isListType t = do
        -- return types
        return (t, [])
    -- if t is dynamic type
    | isDynType t = do
        -- return dynamic typ
        return (ListType DynType, [])
    -- throw error
    | otherwise =
        throwError $ "Error: Type " ++ (show t) ++ " is not a list type!!"

-- get components of recursive type
patternMatchMu :: Var -> Type
    -> StateT Int (Except String) (Type, Constraints)
patternMatchMu var t
    -- if t is type variable
    | isVarType t = do
        -- counter for variable creation
        i <- get
        put (i+1)
        -- create new type variable
        let typeVar = newTypeVar i
        -- build type consisting of new type variables
        let typ = Mu var typeVar
        -- return types and equality relation t =C μVar.T
        return (typ, [Equality t typ])
    -- if t is variant type
    | isMuType t = do
        -- return type
        return (t, [])
    -- if t is dynamic type
    | isDynType t = do
        -- return dynamic type
        return (Mu var DynType, [])
    -- throw error
    | otherwise =
        throwError $ "Error: Type " ++ (show t) ++ " is not a recursive type!!"

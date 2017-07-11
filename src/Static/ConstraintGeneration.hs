module Static.ConstraintGeneration (
    generateConstraints
) where

-- Syntax & Types
import Static.Syntax
import Static.Types

-- Imports
import Control.Monad.State
import Control.Monad.Except
import Data.Maybe

-- generate constraint set and type given a context and expression
generateConstraints :: (Context, Expression)
    -> StateT Int (Except String) (Type, Constraints)

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
        let finalType = fromJust $ varType
        i <- get
        -- replace quantified variables by type variables
        -- instantiation of Damas-Milner
        let (finalType', i') = runState (replaceQuantifiedVariables finalType) i
        put (i')
        -- return type
        return (finalType', [])

-- (Cλ) if expression is a abstraction
generateConstraints (ctx, Abstraction var expr) = do
    -- counter for variable creation
    i <- get
    put (i+1)
    -- create new type variable
    let newVar1 = newTypeVar i
    -- create a binding between the abstraction variable and the new type variable
    let binding = (var, ForAll "" newVar1)
    -- build type assignment with new binding
    let typeAssignment = (binding : ctx, expr)
    -- obtain type and generate constraints for new type assignment
    (exprType, constraints) <- generateConstraints typeAssignment
    -- return arrow type and constraints
    return (ArrowType newVar1 exprType, constraints)

-- (Capp) if expression is a application
generateConstraints (ctx, Application expr1 expr2) = do
    -- counter for variable creation
    i <- get
    put (i+1)
    -- create new type variable
    let newVar = newTypeVar i
    -- build for each expression in the application a type assignment
    let typeAssignment1 = (ctx, expr1)
    let typeAssignment2 = (ctx, expr2)
    -- obtain type and constraints for both expressions
    (t1, constraints1) <- generateConstraints typeAssignment1
    (t2, constraints2) <- generateConstraints typeAssignment2
    -- return type along with all the constraints
    return (newVar, constraints1 ++ constraints2 ++ [Equality t1 (ArrowType t2 newVar)])

-- (C::) if expression is an ascription
generateConstraints (ctx, Ascription expr typ) = do
    -- build type assignment for expression
    let typeAssignment = (ctx, expr)
    -- obtain type and generate constraints for type assignment
    (exprType, constraints) <- generateConstraints typeAssignment
    -- return type along with all the constraints
    return (typ, constraints ++ [Equality exprType typ])

-- (Cλ:) if expression is a annotated abstraction
generateConstraints (ctx, Annotation var typ expr) = do
    -- create a binding between the abstraction variable and the annotated type
    let binding = (var, ForAll "" typ)
    -- build type assignment with new binding
    let typeAssignment = (binding : ctx, expr)
    -- obtain type and generate constraints for new type assignment
    (exprType, constraints) <- generateConstraints typeAssignment
    -- return arrow type and constraints
    return (ArrowType typ exprType, constraints)

-- (Cn) if expression is a integer
generateConstraints (ctx, Int int) = do
    -- return Int type
    return (IntType, [])

-- (Cb) if expression is a boolean
generateConstraints (ctx, Bool bool) = do
    -- return Bool type
    return (BoolType, [])

-- if expression is a let binding
generateConstraints (ctx, Let var expr1 expr2)
    -- (Cletp) if expression is a let binding a value to a variable
     | isValue expr1 || isAnnotation expr1 = do
        -- build type assignment for value
        let typeAssignment1 = (ctx, expr1)
        -- obtain type and generate constraints for type assignment
        (t1, constraints1) <- generateConstraints typeAssignment1
        -- generalize type variables
        let t1' = generalizeTypeVariables t1
        -- build type assignment for value
        let typeAssignment2 = ((var, t1') : ctx, expr2)
        -- obtain type and generate constraints for type assignment
        (t2, constraints2) <- generateConstraints typeAssignment2
        -- return type along with all the constraints
        return (t2, constraints1 ++ constraints2)
    -- (Clet) if expression is a let binding a expression to a variable
    | otherwise = do
        -- (Clet) if expression is a let binding a non-value to a variable
        -- build type assignment for value
        let typeAssignment = (ctx, Application (Abstraction var expr2) expr1)
        -- obtain type and generate constraints for type assignment
        (t, constraints) <- generateConstraints typeAssignment
        -- return type along with all the constraints
        return (t, constraints)


-- if expression is a fixed point
generateConstraints (ctx, Fix expr) = do
    -- counter for variable creation
    i <- get
    put (i+2)
    -- create new type variable
    let newVar1 = newTypeVar i
    let newVar2 = newTypeVar (i+1)
    -- build type assignment
    let typeAssignment1 = (ctx, expr)
    -- obtain type and generate constraints for type assignment
    (t1, constraints) <- generateConstraints typeAssignment1
    return (newVar1, constraints ++ [Equality t1 (ArrowType newVar1 newVar2)])

-- if expression is a recursive let binding
generateConstraints (ctx, LetRec var expr1 expr2) = do
    -- build type assignment
    let typeAssignment = (ctx, Let var (Fix $ Abstraction var expr1) expr2)
    -- obtain type and generate constraints for type assignment
    (t, constraints) <- generateConstraints typeAssignment
    return (t, constraints)

-- (Cif) if expression if a conditional statement
generateConstraints (ctx, If expr1 expr2 expr3) = do
    -- build for each expression in the application a type assignment
    let typeAssignment1 = (ctx, expr1)
    let typeAssignment2 = (ctx, expr2)
    let typeAssignment3 = (ctx, expr3)
    -- obtain type and constraints for both expressions
    (t1, constraints1) <- generateConstraints typeAssignment1
    (t2, constraints2) <- generateConstraints typeAssignment2
    (t3, constraints3) <- generateConstraints typeAssignment3
    -- return type along with all the constraints
    return (t2, constraints1 ++ constraints2 ++ constraints3 ++ [Equality t1 BoolType, Equality t2 t3])

-- if expression is an arithmetic or relational operator
generateConstraints (ctx, expr)
    -- if expression is an addition (C+), subtraction (C-),
    -- multiplication (C*), or division (C/)
    | isArithmeticOperator expr = do
        -- build for each expression in the addition a type assignment
        let typeAssignment1 = (ctx, expr1)
        let typeAssignment2 = (ctx, expr2)
        -- obtain type and constraints for both expressions
        (t1, constraints1) <- generateConstraints typeAssignment1
        (t2, constraints2) <- generateConstraints typeAssignment2
        -- return type along with all the constraints
        return (IntType, constraints1 ++ constraints2 ++
            [Equality t1 IntType, Equality t2 IntType])
    -- if expression is an equality (C==), not equality (C/=), lesser than (C<),
    -- greater than (C>), lesser than or equal to (C<=) or greater than or equal to (C>=) check
    | isRelationalOperator expr = do
        -- build for each expression in the addition a type assignment
        let typeAssignment1 = (ctx, expr1)
        let typeAssignment2 = (ctx, expr2)
        -- obtain type and constraints for both expressions
        (t1, constraints1) <- generateConstraints typeAssignment1
        (t2, constraints2) <- generateConstraints typeAssignment2
        -- return type along with all the constraints
        return (BoolType, constraints1 ++ constraints2 ++
            [Equality t1 IntType, Equality t2 IntType])
    -- retrieve sub expressions from the operator
    where (expr1, expr2) = fromOperator expr

-- (Cunit) if expression is an unit
generateConstraints (ctx, Unit) = do
    -- return type along with all the constraints
    return (UnitType, [])

-- (Cpair) if expression is a pair
generateConstraints (ctx, Pair expr1 expr2) = do
    -- build for each expression in the application a type assignment
    let typeAssignment1 = (ctx, expr1)
    let typeAssignment2 = (ctx, expr2)
    -- obtain type and constraints for both expressions
    (t1, constraints1) <- generateConstraints typeAssignment1
    (t2, constraints2) <- generateConstraints typeAssignment2
    -- return type along with all the constraints
    return (ProductType t1 t2, constraints1 ++ constraints2)

-- (Cfst) if expression is a first projection
generateConstraints (ctx, First expr) = do
    -- counter for variable creation
    i <- get
    put (i+2)
    -- create new type variable
    let newVar1 = newTypeVar i
    let newVar2 = newTypeVar (i+1)
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints) <- generateConstraints typeAssignment
    -- return type along with all the constraints
    return (newVar1, constraints ++ [Equality t (ProductType newVar1 newVar2)])

-- (Csnd) if expression is a second projection
generateConstraints (ctx, Second expr) = do
    -- counter for variable creation
    i <- get
    put (i+2)
    -- create new type variable
    let newVar1 = newTypeVar i
    let newVar2 = newTypeVar (i+1)
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints) <- generateConstraints typeAssignment
    -- return type along with all the constraints
    return (newVar2, constraints ++ [Equality t (ProductType newVar1 newVar2)])

-- (Crecord) if expression is a record
generateConstraints (ctx, Record records) = do
    -- get labels and types
    let (labels, exprs) = fromRecords records
    -- build for each expression a type assignment
    let typeAssignments = map (\x -> (ctx, x)) exprs
    -- obtain type and constraints for both expressions
    results <- mapM generateConstraints typeAssignments
    -- get resulting types and constraints
    let (types, cs) = unzip results
    -- build type
    let ts = zip labels types
    -- return type along with all the constraints
    return (RecordType ts, concat cs)

-- (Cprojection) if expression is a first projection
generateConstraints (ctx, Projection label expr typ) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints) <- generateConstraints typeAssignment
    -- if expression is annotated with a record type
    if isRecordType typ then do
        -- retrieve type
        let RecordType records = typ
        -- obtain type according to tag
        let tagType = lookup label records
        -- if type doesn't exist in record
        if isNothing tagType then do
            let cs = [Equality typ (RecordType [(label, UnitType)])]
            return (UnitType, constraints ++ cs)
        else do
            -- get labels
            let (labels, _) = fromRecordType typ
            -- number of records
            let n = length records
            -- counter for variable creation
            i <- get
            put (i+n+1)
            -- create new type variables
            let typeVars = map newTypeVar [i..i+n]
            -- create record type of type variables
            let listVar = zip labels typeVars
            -- let type of expr be a type variable according to the label
            let finalType = fromJust $ lookup label listVar
            -- return type along with all the constraints
            return (finalType, constraints ++
                [Equality (RecordType listVar) t, Equality typ t])
    -- if expression is annotated with a wrong type
    else do
        let typ' = RecordType [(label, UnitType)]
        return (UnitType, constraints ++ [Equality typ typ'])

-- (Ccase) if expression is a case
generateConstraints (ctx, Case expr (var1, expr1) (var2, expr2)) = do
    -- counter for variable creation
    i <- get
    put (i+3)
    -- create new type variable
    let newVar1 = newTypeVar i
    let newVar2 = newTypeVar (i+1)
    let newVar3 = newTypeVar (i+2)
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints) <- generateConstraints typeAssignment
    -- build for each expression a type assignment
    let typeAssignment1 = ((var1, newVar1) : ctx, expr1)
    let typeAssignment2 = ((var2, newVar2) : ctx, expr2)
    -- obtain type and constraints for both expressions
    (t1, constraints1) <- generateConstraints typeAssignment1
    (t2, constraints2) <- generateConstraints typeAssignment2
    -- return type along with all the constraints
    return (t1, constraints ++ constraints1 ++ constraints2 ++
        [Equality t (SumType newVar1 newVar2), Equality t1 t2])

-- (Cinl) if expression is a left tag
generateConstraints (ctx, LeftTag expr typ) = do
    -- counter for variable creation
    i <- get
    put (i+2)
    -- create new type variable
    let newVar1 = newTypeVar i
    let newVar2 = newTypeVar (i+1)
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints) <- generateConstraints typeAssignment
    -- return type along with all the constraints
    return (typ, constraints ++
        [Equality typ (SumType newVar1 newVar2), Equality t newVar1])

-- (Cinr) if expression is a right tag
generateConstraints (ctx, RightTag expr typ) = do
    -- counter for variable creation
    i <- get
    put (i+2)
    -- create new type variable
    let newVar1 = newTypeVar i
    let newVar2 = newTypeVar (i+1)
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints) <- generateConstraints typeAssignment
    -- return type along with all the constraints
    return (typ, constraints ++
        [Equality typ (SumType newVar1 newVar2), Equality t newVar2])

-- (Ccasevariant) if expression is a variant case
generateConstraints (ctx, CaseVariant expr alternatives) = do
    -- number of alternatives
    let n = length alternatives
    -- counter for variable creation
    i <- get
    put (i+n+1)
    -- create new type variables
    let typeVars = map newTypeVar [i..i+n]
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints) <- generateConstraints typeAssignment
    -- build for each expression a type assignment
    let typeAssignments = map
            (\x -> let
                -- get type variable from alternative
                var = snd3 $ snd x
                -- get expression from alternative
                expr' = trd3 $ snd x
                -- get type variable
                typ = fst x
                -- add to context variable with new type
                in ((var, typ) : ctx, expr'))
            $ zip typeVars alternatives
    -- obtain type and constraints for both expressions
    results <- mapM generateConstraints typeAssignments
    -- get resulting types and constraints
    let (ts, cs) = unzip results
    -- build type consisting of new type variables
    let list = map
            (\x -> let
                -- get label from alternatives
                label = fst3 $ snd x
                -- get type variable
                typ = fst x
                -- build variant type
                in (label, typ))
            $ zip typeVars alternatives
    -- type of expr must be variant type
    let cs1 = [Equality t (VariantType list)]
    -- resulting types from each alternative must be equal
    let cs2 = map (\x -> Equality (ts!!0) x) (tail ts)
    -- return type along with all the constraints
    return (ts !! 0, constraints ++ (concat cs) ++ cs1 ++ cs2)

-- (Ctag) if expression is a tag
generateConstraints (ctx, Tag label expr typ) = do
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints) <- generateConstraints typeAssignment
    -- if expression is annotated with a variant type
    if isVariantType typ then do
        -- retrieve type
        let VariantType list = typ
        -- obtain type according to tag
        let tagType = lookup label list
        -- if type doesn't exist in variant
        if isNothing tagType then do
            let cs = [Equality typ (VariantType [(label, t)])]
            return (typ, constraints ++ cs)
        else do
            let finalType = fromJust tagType
            -- return type along with all the constraints
            return (typ, constraints ++ [Equality finalType t])
    -- if expression is annotated with a wrong type
    else do
        let typ' = VariantType [(label, t)]
        return (typ', constraints ++ [Equality typ typ'])

-- (Cfold) if expression is a fold
generateConstraints (ctx, Fold typ expr) = do
    -- counter for variable creation
    i <- get
    put (i+1)
    -- create new type variable
    let newVar1 = newTypeVar i
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints) <- generateConstraints typeAssignment
    -- unfold type
    let (Mu var typ') = typ
    let t' = unfoldType (var, typ) typ'
    -- return type along with all the constraints
    return (typ, constraints ++    [Equality t' t])

-- (Cfold) if expression is a fold
generateConstraints (ctx, Unfold typ expr) = do
    -- counter for variable creation
    i <- get
    put (i+1)
    -- create new type variable
    let newVar1 = newTypeVar i
    -- build type assignment
    let typeAssignment = (ctx, expr)
    -- obtain type and constraints for type assignment
    (t, constraints) <- generateConstraints typeAssignment
    -- unfold type
    let (Mu var typ') = typ
    let t' = unfoldType (var, typ) typ'
    -- return type along with all the constraints
    return (t', constraints ++    [Equality typ t])

-- Replace type parameters with type variables
replaceQuantifiedVariables :: Type -> State Int Type
replaceQuantifiedVariables (ForAll var typ) = do
    -- counter for variable creation
    i <- get
    put (i+1)
    -- obtain new type by replacing matched type parameters with fresh type variable
    let typ' = substituteType (VarType var, newTypeVar i) typ
    -- recursive call
    replaceQuantifiedVariables typ'
-- return when no more ForAll quantifier
replaceQuantifiedVariables e = return e

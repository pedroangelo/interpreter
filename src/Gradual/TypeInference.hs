module Gradual.TypeInference (
    inferType,
    insertTypeInformation
) where

-- Syntax & Types
import Gradual.Syntax
import Gradual.Types
import Gradual.Examples

-- Type Inference
import Gradual.ConstraintGeneration
import Gradual.ConstraintUnification

-- Imports
import Control.Monad.State
import Control.Monad.Except
import Data.Either
import Data.List

-- infer the type of the expression
inferType :: Expression -> Either String Type
inferType expr = do
    result <- typeInference expr
    return $ fst result

-- insert type information to each term in the expression
insertTypeInformation :: Expression -> Either String Expression
insertTypeInformation expr = do
    result <- typeInference expr
    return $ snd result

-- type inference procedure
typeInference :: Expression -> Either String (Type, Expression)
typeInference expr = do
    -- build type assignment from expression and expression
    let ta = ([], expr)
    -- generate constraints
    cg <- runExcept $ runStateT (generateConstraints ta) 1
    -- retrieve constraints
    let ((typ, constraints, expr_typed), counter) = cg
    -- unify constraints and generate substitutions
    cu <- runExcept $ unifyConstraints [] (reverse constraints) counter
    -- retrieve gradual types and substitutions
    let (gtypes, substitutions) = cu
    -- filter gradual type variables
    let gtypes' = nub $ concat $ map (\x -> map (VarType) $ freeVariables x) gtypes
    -- add substitutions from types present in gtypes to dynamic type
    let substitutions' = (map (\x -> (x, DynType)) gtypes') ++ substitutions
    -- replace unconstrained type variables by type parameters
    -- discover final type by applying all substitutions to expression type t
    let finalType = foldr substituteType typ substitutions'
    -- replace unconstrained type variables by type parameters
    -- discover final types by applying all substitutions to each type ascription and type information in the expression
    let typedExpr = substituteTypedExpression substitutions' expr_typed
    return (finalType, typedExpr)

module TypeInference (
	inferType,
	typeExpression
) where

-- Syntax & Types
import Syntax
import Types
import Examples

-- Type Inference
import ConstraintGeneration
import ConstraintUnification

-- Imports
import Control.Monad.State

-- infer the type of the expression
inferType :: Expression -> Type
inferType = fst . typeInference

-- insert type information to each term in the expression
typeExpression :: Expression -> Expression
typeExpression = snd . typeInference

-- type inference procedure
typeInference :: Expression -> (Type, Expression)
typeInference expr =
	let
		-- build type assignment from expression and expression
		typeAssignment = ([], expr)
		-- generate constraints
		((typ, constraints, expr_typed), counter) = runState (generateConstraints typeAssignment) 1
		-- unify constraints and generate substitutions
		substitutions = unifyConstraints (reverse constraints) counter
		-- replace unconstrained type variables by type parameters
		-- discover final type by applying all substitutions to expression type t
		finalType = insertTypeParameters $ foldr instantiateTypeVariable typ substitutions
		-- replace unconstrained type variables by type parameters
		-- discover final types by applying all substitutions to each type ascription and type information in the expression
		typedExpr = substituteTypedExpression substitutions expr_typed
	in (finalType, typedExpr)

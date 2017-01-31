module TypeInference where

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
inferType expr =
	let
		-- build type assignment from expression and expression
		typeAssignment = ([], expr)
		-- generate constraints
		((typ, constraints), counter) = runState (generateConstraints typeAssignment) 1
		-- unify constraints and generate substitutions
		substitutions = unifyConstraints (reverse constraints) counter
		-- replace unconstrained type variables by type parameters
		-- discover final type by applying all substitutions to expression type t
		finalType = insertTypeParameters $ foldr instantiateTypeVariable typ substitutions
	in finalType

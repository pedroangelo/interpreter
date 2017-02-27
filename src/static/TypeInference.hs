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
import Control.Monad.Except

-- infer the type of the expression
inferType :: Expression -> Either String Type
inferType expr = do
	-- build type assignment from expression and expression
	let typeAssignment = ([], expr)
	-- generate constraints
	cg <- runExcept $ runStateT (generateConstraints typeAssignment) 1
	-- retrieve constraints
	let ((typ, constraints), counter) = cg
	-- unify constraints and generate substitutions
	cu <- runExcept $ unifyConstraints (reverse constraints) counter
	-- retrieve substitutions
	let substitutions = cu
	-- replace unconstrained type variables by type parameters
	-- discover final type by applying all substitutions to expression type t
	let finalType = insertTypeParameters $ foldr substituteType typ substitutions
	return finalType

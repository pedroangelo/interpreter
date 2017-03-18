module TypeInference (
	inferType,
	insertTypeInformation
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
	let gtypes' = nub $ concat $ map
		(\x -> let
			-- get list of type variables
			(exclude, include) = countTypeVariable x
			in map (VarType) $ (nub include) \\ exclude)
		gtypes
	-- add substitutions from types present in gtypes to dynamic type
	let substitutions' = (map (\x -> (x, DynType)) gtypes') ++ substitutions
	-- replace unconstrained type variables by type parameters
	-- discover final type by applying all substitutions to expression type t
	let finalType = generalizeTypeVariables $ foldr substituteType typ substitutions'
	-- replace unconstrained type variables by type parameters
	-- discover final types by applying all substitutions to each type ascription and type information in the expression
	let typedExpr = substituteTypedExpression substitutions' expr_typed
	return (finalType, typedExpr)

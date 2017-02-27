module Interpreter (
	interpret
) where

-- Syntax & Types
import Syntax
import Types
import Examples

-- Type Inference
import TypeInference

-- Cast Insertion
import CastInsertion

-- Evaluation
import Evaluation

-- Imports
import Data.Either

-- run interpreter for given expression
interpret :: Expression -> IO ()
interpret expr = do
	-- get type of expression
	let ti = inferType expr
	-- if expression is ill typed
	if isLeft ti then do
		-- print error
		let (Left err) = ti
		putStrLn err
		return ()
	-- if expression is well typed
	else do
		-- print type
		let (Right typ) = ti
		putStrLn $ "Expression type: " ++ (show typ)
		-- insert casts
		let (Right typedExpr) = insertTypeInformation expr
		let casts = removeTypeInformation $ insertCasts typedExpr
		putStrLn $ "\nCast insertion: " ++ (show casts)
		-- run evaluation
		let result = evaluate casts
		putStrLn $ "\nEvaluation result: " ++ (show result)

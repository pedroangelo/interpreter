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

-- Pretty Printing
import PrettyPrinter

-- Parser
import Parser

-- Imports
import Data.Either
import Text.Parsec

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

runCode :: String -> IO ()
runCode string = do
	-- parse string to expression
	let parsed = parse expressionParser "" string
	-- if parsing failed
	if isLeft parsed then do
		-- print error
		let (Left parseError) = parsed
		putStrLn $ show parseError
		return ()
	else do
		-- get expression
		let (Right expr) = parsed
		-- infer type
		let ti = inferType expr
		-- if expression is ill-typed
		if isLeft ti then do
			-- print error
			let (Left typeError) = ti
			putStrLn typeError
			return ()
		-- if expression is well typed
		else do
			-- print type
			let (Right typ) = ti
			putStrLn $ "Expression type: " ++ (show $ prettyType typ)
			-- insert casts
			let (Right typedExpr) = insertTypeInformation expr
			let casts = removeTypeInformation $ insertCasts typedExpr
			putStrLn $ "\nCast insertion: " ++ (show $ prettyExpression casts)
			-- run evaluation
			let result = evaluate casts
			putStrLn $ "\nEvaluation result: " ++ (show $ prettyExpression result)

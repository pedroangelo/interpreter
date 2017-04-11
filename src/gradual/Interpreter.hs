module Interpreter (
	interpret,
	runCode,
	runFile
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
interpret expr = interpretCode False expr

-- run interpreter for given expression
interpretCode :: Bool -> Expression -> IO ()
interpretCode parameter expr = do
	let prettyE = if parameter then (\x -> show $ prettyExpression x) else show
	let prettyT = if parameter then (\x -> show $ prettyType x ) else show
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
		-- print expression
		putStrLn $ "Expression: " ++ prettyE expr
		-- print type
		let (Right typ) = ti
		putStrLn $ "\nExpression type: " ++ prettyT typ
		-- insert casts
		let (Right typedExpr) = insertTypeInformation expr
		let casts = removeTypeInformation $ insertCasts typedExpr
		putStrLn $ "\nCast insertion: " ++ prettyE casts
		-- run evaluation
		let result = evaluate casts
		putStrLn $ "\nEvaluation result: " ++ prettyE result

runCode :: String -> IO ()
runCode string = do
	-- parse string
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
		-- run interpreter
		interpretCode True expr

runFile :: FilePath -> IO ()
runFile filePath = do
	-- get file contents
	fileContents <- readFile filePath
	-- parse contents
	let parsed = parse expressionParser "" fileContents
	-- if parsing failed
	if isLeft parsed then do
		-- print error
		let (Left parseError) = parsed
		putStrLn $ show parseError
		return ()
	else do
		-- get expression
		let (Right expr) = parsed
		-- run interpreter
		interpretCode True expr

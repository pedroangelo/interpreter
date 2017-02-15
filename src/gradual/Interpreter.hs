module Interpreter (
	interpret
) where

-- Syntax & Types
import Syntax
import Types
import Examples

-- TypeInference
import TypeInference

-- Cast Insertion
import CastInsertion

-- Evaluation
import Evaluation

-- Imports
import Data.Either

interpret :: Expression -> IO ()
interpret expr = do
	let ti = inferType expr
	if isLeft ti
		then do
			let (Left err) = ti
			putStrLn err
			return ()
		else do
			let (Right typ) = ti
			putStrLn $ "Expression type: " ++ (show typ)
			let (Right typedExpr) = insertTypeInformation expr
			let casts = removeTypeInformation $ insertCasts typedExpr
			putStrLn $ "\nCast insertion: " ++ (show casts)
			let result = evaluate casts
			putStrLn $ "\nEvaluation result: " ++ (show result)

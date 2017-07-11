module Gradual.Interpreter (
    interpret,
    runCode,
    runFile
) where

-- Syntax & Types
import Gradual.Syntax
import Gradual.Types
import Gradual.Examples

-- Type Inference
import Gradual.TypeInference

-- Cast Insertion
import Gradual.CastInsertion

-- Evaluation
import Gradual.Evaluation

-- Pretty Printing
import Gradual.PrettyPrinter

-- Parser
import Gradual.Parser

-- Imports
import Data.Either
import Text.Parsec

-- run interpreter for given expression
interpret :: Expression -> IO ()
interpret = interpretCode False

-- run interpreter for given expression
interpretCode :: Bool -> Expression -> IO ()
interpretCode parameter expr = do
    let prettyE = if parameter then show . prettyExpression else show
    let prettyT = if parameter then show . prettyType else show
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
        print parseError
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
        print parseError
        return ()
    else do
        -- get expression
        let (Right expr) = parsed
        -- run interpreter
        interpretCode True expr

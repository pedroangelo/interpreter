module Gradual.Parser (
    expressionParser,
    typeParser
) where

-- Syntax & Types
import Gradual.Syntax
import Gradual.Types
import Gradual.Examples

-- Parsec
import Text.Parsec hiding (label, labels)
import Text.Parsec.String (Parser)
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language (emptyDef)
import Text.ParserCombinators.Parsec.Combinator
import qualified Text.Parsec.Token as Token

-- language definition for lexer
languageDefinition :: Token.LanguageDef ()
languageDefinition = emptyDef {
    Token.commentStart = "{-",
    Token.commentEnd = "-}",
    Token.commentLine = "--",
    Token.nestedComments = False,
    Token.identStart = lower,
    Token.identLetter = alphaNum <|> oneOf "_'",
    Token.opStart = oneOf ":!#$%&*+./<=>?@\\^|-~",
    Token.opLetter = oneOf ":!#$%&*+./<=>?@\\^|-~",
    Token.reservedNames = ["true", "false", "let", "in", "fix", "letrec",
                            "if", "then", "else", "unit", "as", "case", "of",
                            "nil", "cons", "isnil", "head", "tail", "fold",
                            "unfold", "Int", "Bool", "Unit", "Dyn", "forall", "rec"],
    Token.reservedOpNames = ["\\", ".",":","::","=","+","-","*","-","/","==",
                                "/=","<",">","<=",">=","->","{","}","[","]"],
    Token.caseSensitive = True }

-- create lexer according to language definition
lexer :: Token.TokenParser ()
lexer = Token.makeTokenParser languageDefinition

-- identifiers
identifier :: Parser String
identifier = Token.identifier lexer

-- reserved names
reserved :: String -> Parser ()
reserved = Token.reserved lexer

-- reserved operators
reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp lexer

-- natural numbers
natural :: Parser Integer
natural = Token.natural lexer

-- white space
whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace lexer

-- parentheses
parens :: Parser a -> Parser a
parens = Token.parens lexer

-- braces
braces :: Parser a -> Parser a
braces = Token.braces lexer

-- angles
angles :: Parser a -> Parser a
angles = Token.angles lexer

-- brackets
brackets :: Parser a -> Parser a
brackets = Token.brackets lexer

-- separated by ;
semiSep :: Parser a -> Parser [a]
semiSep = Token.semiSep lexer

-- comma
comma :: Parser String
comma = Token.comma lexer

-- colon
colon :: Parser String
colon = Token.colon lexer

-- dot
dot :: Parser String
dot = Token.dot lexer

-- separated by ,
commaSep1 :: Parser a -> Parser [a]
commaSep1 = Token.commaSep1 lexer


-- label
label :: Parser String
label = do
    { a <- upper
    ; as <- many $ alphaNum <|> oneOf "_'"
    ; whiteSpace
    ; return (a:as) }

-- Expression Parser
expressionParser = do
    whiteSpace
    e <- expression
    whiteSpace
    eof
    return e

-- expressions
expression :: Parser Expression
expression =
    try abstractionExpression <|>
    try ascriptionExpression <|>
    annotationExpression <|>
    letExpression <|>
    fixExpression <|>
    letrecExpression <|>
    ifExpression <|>
    try projectionTupleExpression <|>
    try projectionRecordExpression <|>
    caseExpression <|>
    nilExpression <|>
    try emptyListExpression <|>
    consExpression <|>
    try consOperatorExpression <|>
    listExpression <|>
    isNilExpression <|>
    headExpression <|>
    tailExpression <|>
    foldExpression <|>
    unfoldExpression <|>
    operatorExpression <?> "expression"

-- force parentheses in some expressions
parensExpression :: Parser Expression
parensExpression =
    variableExpression <|>
    intExpression <|>
    boolExpression <|>
    unitExpression <|>
    try tupleExpression <|>
    try recordExpression <|>
    tagExpression <|>
    parens expression <?> "delimited expression"

-- operators
operatorExpression :: Parser Expression
operatorExpression = buildExpressionParser operators applicationExpression

-- application
applicationExpression :: Parser Expression
applicationExpression = do
    { es <- many1 parensExpression
    ; return $ foldl1 Application es } <?> "application"

-- variable
variableExpression :: Parser Expression
variableExpression = do
    { x <- identifier
    ; return $ Variable x } <?> "variable"

-- abstraction
abstractionExpression :: Parser Expression
abstractionExpression = do
    { reservedOp "\\"
    ; v <- identifier
    ; reservedOp "."
    ; e <- expression
    ; return $ Abstraction v e } <?> "abstraction"

-- annotated abstraction
annotationExpression :: Parser Expression
annotationExpression = do
    { reservedOp "\\"
    ; v <- identifier
    ; reservedOp ":"
    ; t <- typeParser
    ; reservedOp "."
    ; e <- expression
    ; return $ Annotation v t e } <?> "annotated abstraction"

-- ascription
ascriptionExpression = do
    { e <- parensExpression
    ; reservedOp "::"
    ; t <- typeParser
    ; return $ Ascription e t } <?> "ascription"

-- integer
intExpression :: Parser Expression
intExpression = do
    { n <- natural
    ; return $ Int $ fromInteger n } <?> "integer"

-- boolean
boolExpression :: Parser Expression
boolExpression =
    do {b <- reserved "true"; return $ Bool True} <|>
    do {b <- reserved "false"; return $ Bool False} <?> "boolean"

-- let binding
letExpression :: Parser Expression
letExpression = do
    { reserved "let"
    ; v <- identifier
    ; reservedOp "="
    ; e1 <- expression
    ; reserved "in"
    ; e2 <- expression
    ; return $ Let v e1 e2 } <?> "let binding"

-- fixed point
fixExpression :: Parser Expression
fixExpression = do
    { reserved "fix"
    ; e <- parensExpression
    ; return $ Fix e } <?> "fixed point"

-- let binding
letrecExpression :: Parser Expression
letrecExpression = do
    { reserved "letrec"
    ; v <- identifier
    ; reservedOp "="
    ; e1 <- expression
    ; reserved "in"
    ; e2 <- expression
    ; return $ LetRec v e1 e2 } <?> "recursive let binding"

-- conditional statements
ifExpression :: Parser Expression
ifExpression = do
    { reserved "if"
    ; e1 <- expression
    ; reserved "then"
    ; e2 <- expression
    ; reserved "else"
    ; e3 <- expression
    ; return $ If e1 e2 e3 } <?> "conditional statement"

-- unit
unitExpression :: Parser Expression
unitExpression = do
    { reserved "unit"
    ; return $ Unit } <?> "unit"

-- tuple
tupleExpression :: Parser Expression
tupleExpression = (parens $ do
    { e <- expression
    ; comma
    ; es <- commaSep1 expression
    ; return $ Tuple (e:es) }) <?> "tuple"

-- projection from tuples
projectionTupleExpression :: Parser Expression
projectionTupleExpression = do
    { e <- parensExpression
    ; reservedOp "."
    ; i <- natural
    ; reserved "as"
    ; t <- typeParser
    ; return $ ProjectionTuple (fromInteger i) e t } <?> "tuple projection"

-- record
recordExpression :: Parser Expression
recordExpression = (braces $ do
    { es <- commaSep1 assignment
    ; return $ Record es }) <?> "record"

-- projection from records
projectionRecordExpression :: Parser Expression
projectionRecordExpression = do
    { e <- parensExpression
    ; reservedOp "."
    ; l <- identifier
    ; reserved "as"
    ; t <- typeParser
    ; return $ ProjectionRecord l e t } <?> "record projection"

assignment :: Parser (Var, Expression)
assignment = do
    { var <- identifier
    ; reservedOp "="
    ; t <- expression
    ; return $ (var, t) } <?> "type variable assignment"

-- variant case
caseExpression :: Parser Expression
caseExpression = do
    { reserved "case"
    ; e <- expression
    ; reserved "of"
    ; alternatives <- many1 alternative
    ; return $ CaseVariant e alternatives } <?> "case"

-- alternatives to case
alternative :: Parser Alternative
alternative = do
    { reservedOp "|"
    ; l <- label
    ; v <- identifier
    ; reservedOp "->"
    ; e <- expression
    ; return $ (l, v, e) } <?> "alternative"

-- tag
tagExpression :: Parser Expression
tagExpression = do
    { reservedOp "<"
    ; l <- label
    ; reservedOp "="
    ; e <- parensExpression
    ; reservedOp ">"
    ; reserved "as"
    ; t <- typeParser
    ; return $ Tag l e t } <?> "tag"

-- nil
nilExpression :: Parser Expression
nilExpression = do
    { reserved "nil"
    ; reservedOp "["
    ; t <- typeParser
    ; reservedOp "]"
    ; return $ Nil t } <?> "empty list (nil)"

-- empty list
emptyListExpression :: Parser Expression
emptyListExpression = do
    { reservedOp "["
    ; reservedOp "]"
    ; reserved "as"
    ; t <- typeParser
    ; return $ Nil t } <?> "empty list"

-- cons
consExpression :: Parser Expression
consExpression = do
    { reserved "cons"
    ; reservedOp "["
    ; t <- typeParser
    ; reservedOp "]"
    ; e1 <- parensExpression
    ; e2 <- parensExpression
    ; return $ Cons t e1 e2 } <?> "list constructor"

-- cons operator
consOperatorExpression :: Parser Expression
consOperatorExpression = do
    { e1 <- parensExpression
    ; reservedOp ":"
    ; e2 <- parensExpression
    ; reserved "as"
    ; t <- typeParser
    ; return $ Cons t e1 e2 } <?> "list constructor operator"

-- list
listExpression :: Parser Expression
listExpression = do
    { reservedOp "["
    ; es <- commaSep1 expression
    ; reservedOp "]"
    ; reserved "as"
    ; t <- typeParser
    ; return $ foldr (Cons t) (Nil t) es } <?> "list"

-- isnil
isNilExpression :: Parser Expression
isNilExpression = do
    { reserved "isnil"
    ; reservedOp "["
    ; t <- typeParser
    ; reservedOp "]"
    ; e <- parensExpression
    ; return $ IsNil t e } <?> "test for empty list"

-- head
headExpression :: Parser Expression
headExpression = do
    { reserved "head"
    ; reservedOp "["
    ; t <- typeParser
    ; reservedOp "]"
    ; e <- parensExpression
    ; return $ Head t e } <?> "head of a list"

-- tail
tailExpression :: Parser Expression
tailExpression = do
    { reserved "tail"
    ; reservedOp "["
    ; t <- typeParser
    ; reservedOp "]"
    ; e <- parensExpression
    ; return $ Tail t e } <?> "tail of a list"

-- fold
foldExpression :: Parser Expression
foldExpression = do
    { reserved "fold"
    ; reservedOp "["
    ; t <- typeParser
    ; reservedOp "]"
    ; e <- expression
    ; return $ Fold t e } <?> "fold"

-- fold
unfoldExpression :: Parser Expression
unfoldExpression = do
    { reserved "unfold"
    ; reservedOp "["
    ; t <- typeParser
    ; reservedOp "]"
    ; e <- expression
    ; return $ Unfold t e } <?> "unfold"

-- operator table
operators = [
    [binary "*" Multiplication AssocLeft,
    binary "/" Division AssocLeft],
    [binary "+" Addition AssocLeft,
    binary "-" Subtraction AssocLeft],
    [binary "==" Equal AssocNone,
    binary "/=" NotEqual AssocNone,
    binary "<" LesserThan AssocNone,
    binary ">" GreaterThan AssocNone,
    binary "<=" LesserEqualTo AssocNone,
    binary ">=" GreaterEqualTo AssocNone]]

binary string operator associativity =
    Infix (do {reservedOp string; return operator}) associativity

-- Type Parser
typeParser = typ

typ :: Parser Type
typ =
    arrowOperator

parensType :: Parser Type
parensType =
    varType <|>
    intType <|>
    boolType <|>
    unitType <|>
    dynType <|>
    muType <|>
    try tupleType <|>
    recordType <|>
    variantType <|>
    listType <|>
    parens typ

-- Type variable: Var
varType :: Parser Type
varType = do
    { var <- identifier
    ; return $ VarType var } <?> "type variable"

-- Arrow type: Type -> Type
arrowOperator :: Parser Type
arrowOperator = buildExpressionParser
    [[binary "->" ArrowType AssocRight]] parensType

-- Integer type: Int
intType :: Parser Type
intType = do
    { reserved "Int"
    ; return IntType } <?> "integer type"

-- Boolean type: Bool
boolType :: Parser Type
boolType = do
    { reserved "Bool"
    ; return BoolType } <?> "boolean type"

-- Dynamic type: Dyn
dynType :: Parser Type
dynType = do
    { reserved "Dyn"
    ; return DynType } <?> "dynamic type"

-- Unit type: Unit
unitType :: Parser Type
unitType = do
    { reserved "Unit"
    ; return UnitType } <?> "unit type"

-- Tuple type: (Types)
tupleType :: Parser Type
tupleType = (parens $ do
    { t <- typ
    ; comma
    ; ts <- commaSep1 typ
    ; return $ TupleType (t:ts) }) <?> "tuple type"

-- Record type: {Labels:Types}
recordType :: Parser Type
recordType = (braces $ do
    { ts <- commaSep1 (do
        { var <- identifier
        ; reservedOp ":"
        ; t <- typ
        ; return (var, t)})
    ; return $ RecordType ts }) <?> "record type"

-- Variant type: <Labels:Types>
variantType :: Parser Type
variantType = (angles $ do
    { ts <- commaSep1 (do
        { var <- label
        ; reservedOp ":"
        ; t <- typ
        ; return (var, t)})
    ; return $ VariantType ts }) <?> "variant type"

-- List type: [Type]
listType :: Parser Type
listType = (brackets $ do
    { t <- typ
    ; return $ ListType t }) <?> "list type"

-- Recursive type: rec Var.Types
muType :: Parser Type
muType = do
    { reserved "rec"
    ; var <- identifier
    ; reservedOp "."
    ; t  <- typ
    ; return $ Mu var t } <?> "recursive type"

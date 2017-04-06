module Parser where

-- Syntax & Types
import Syntax
import Types
import Examples

-- Parsec
import Text.Parsec
import Text.Parsec.String (Parser)
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language (emptyDef)
import Text.ParserCombinators.Parsec.Combinator
import qualified Text.Parsec.Token as Token

-- language definition for lexer
languageDefinition :: Token.LanguageDef ()
languageDefinition = emptyDef {
	Token.commentStart    = "{-",
	Token.commentEnd      = "-}",
	Token.commentLine     = "--",
	Token.nestedComments  = False,
	Token.identStart      = letter,
	Token.identLetter     = alphaNum <|> oneOf "_'",
	Token.opStart         = oneOf ":!#$%&*+./<=>?@\\^|-~",
	Token.opLetter        = oneOf ":!#$%&*+./<=>?@\\^|-~",
	Token.reservedNames   = ["let", "in", "fix", "letrec", "if", "then", "else",
	 						"unit",	"as", "case", "of", "fold", "unfold",
							"true", "false", "bool", "int", "?", "forall", "mu"],
	Token.reservedOpNames = ["\\", ".",":","::","=","+","-","*","-","/","==",
							"/=","<",">","<=",">=","->","{","}","[","]"],
	Token.caseSensitive   = True }

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
	annotationExpression <|>
	try ascriptionExpression <|>
	letExpression <|>
	fixExpression <|>
	letrecExpression <|>
	ifExpression <|>
	try projectionTupleExpression <|>
	try projectionRecordExpression <|>
	caseExpression <|>
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
	; e <- expression
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
	; reservedOp "<"
	; l <- identifier
	; reservedOp "="
	; v <- identifier
	; reservedOp ">"
	; reservedOp "=>"
	; e <- expression
	; return $ (l, v, e) } <?> "alternative"

-- tag
tagExpression :: Parser Expression
tagExpression = do
	{ reservedOp "<"
	; l <- identifier
	; reservedOp "="
	; e <- parensExpression
	; reservedOp ">"
	; reserved "as"
	; t <- typeParser
	; return $ Tag l e t } <?> "tag"

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
typeParser = buildExpressionParser typeOperators typ

typ :: Parser Type
typ =
	varType <|>
	intType <|>
	boolType <|>
	unitType <|>
	dynType <|>
	forAllType <|>
	muType <|>
	tupleType <|>
	recordType <|>
	variantType

-- type variable
varType :: Parser Type
varType = do
	{ var <- identifier
	; return $ VarType var } <?> "type variable"

-- int type
intType :: Parser Type
intType = do
	{ reserved "int"
	; return IntType } <?> "integer type"

-- bool type
boolType :: Parser Type
boolType = do
	{ reserved "bool"
	; return BoolType } <?> "boolean type"

-- dynamic type
dynType :: Parser Type
dynType = do
	{ reserved "?"
	; return DynType } <?> "dynamic type"

-- unit type
unitType :: Parser Type
unitType = do
	{ reserved "unit"
	; return UnitType } <?> "unit type"

-- for all quantifier
forAllType :: Parser Type
forAllType = do
	{ reserved "forall"
	; var <- identifier
	; reservedOp "."
	; t  <- typeParser
	; return $ ForAll var t } <?> "for all quantifier"

-- recursive type
muType :: Parser Type
muType = do
	{ reserved "mu"
	; var <- identifier
	; reservedOp "."
	; t  <- typeParser
	; return $ Mu var t } <?> "recursive type"

-- tuple type
tupleType :: Parser Type
tupleType = (parens $ do
	{ t <- typeParser
	; comma
	; ts <- commaSep1 typeParser
	; return $ TupleType (t:ts) }) <?> "tuple type"

-- record type
recordType :: Parser Type
recordType = (braces $ do
	{ ts <- commaSep1 binding
	; return $ RecordType ts }) <?> "record type"

-- variant type
variantType :: Parser Type
variantType = (angles $ do
	{ ts <- commaSep1 binding
	; return $ VariantType ts }) <?> "variant type"

-- binding of variable with type
binding :: Parser (Var, Type)
binding = do
	{ var <- identifier
	; reservedOp ":"
	; t <- typeParser
	; return $ (var, t) } <?> "type variable binding"

-- type operators (arrow)
typeOperators = [[binary "->" ArrowType AssocRight]]

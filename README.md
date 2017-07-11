# interpreter
Interpreter for a gradually typed functional language

### Instalation
Install stack by following the guide in [Haskell Tool Stack](https://www.haskellstack.org/).
```
$ wget -qO- https://get.haskellstack.org/ | sh
```
Clone repository
```
$ git clone git@github.com:pedroangelo/interpreter.git
```
Setup stack
```
$ cd interpreter/
$ stack setup
```
### Load interpreter module
```
$ cd src/
$ stack ghci
```
```
> :l Gradual.Interpreter
```
### Interpret a program from the command line:
```
*Gradual.Interpreter> :t runCode
runCode :: String -> IO ()
*Gradual.Interpreter> runCode <program>
```
Example:
```
*Gradual.Interpreter> runCode "(\\x : Dyn . 1 + x) true"
Expression: (\x : Dyn . 1 + x) True

Expression type: Int

Cast insertion: ((\x : Dyn . (1 : Int => Int) + (x : Dyn => Int)) : (Dyn -> Int) => (Dyn -> Int)) (True : Bool => Dyn)

Evaluation result: Blame: cannot cast from BoolType to IntType
```
### Interpret a program from a file:
```
*Gradual.Interpreter> :t runFile
runFile :: FilePath -> IO ()
*Gradual.Interpreter> runFile <filename>
```

The syntax that the interpreter accepts is described below.

### Language syntax
Expressions
```
Expressions e ::= var                                   variable
                | \var . e                              abstraction
                | e e                                   application
                | \var : T . e                          annotated abstraction
                | e :: T                                ascription
                | integer                               integer
                | boolean                               boolean
                | let var = e in e                      let binding
                | fix e                                 fixed point
                | letrec var = e in e                   recursive let-binding
                | if e then e else e                    conditional statement
                | e arithop e                           arithmetic operator
                | e relatop e                           relational operator
                | unit                                  unit
                | (tuples)                              tuple
                | e.integer as T                        tuple projection
                | {records}                             record
                | e.var as T                            record projection
                | case e of alternatives                case
                | <label = e> as T                      tag
                | nil [T]                               nil
                | [] as T                               empty list
                | cons [T] e e                          cons
                | e : e as T                            cons operator
                | [list] as T                           list
                | isnil [T] e                           isnil
                | head [T] e                            head
                | tail [] e                             tail
                | fold [T] e                            fold
                | unfold [T] e                          unfold

integer ::= 0 | 1 | 2 | ...
boolean ::= true | false
arithop ::= + | - | * | /
relatop ::= == | /= | < | > | <= | >=
tuples ::= e, e | e, tuples
records ::= var = e | var = e, records
alternatives ::= | label var -> e
               | | label var -> e alternatives
list ::= e | e, list
```
`var` represents a variable, which can be any string starting with a lower case alphabetic character followed by alphanumeric characters, an underscore or quotation mark.

`integer` represents a positive integer (i.e. 0, 1, 2, ...).

`boolean` represents a boolean value, either true or false.

`label` represents a string starting with an upper case alphabetic character followed by alphanumeric characters, an underscore or quotation mark.

Types
```
Types T ::= var                                         type variable
          | T -> T                                      arrow type
          | Int                                         integer type
          | Bool                                        boolean type
          | Dyn                                         dynamic type
          | Unit                                        unit type
          | rec var . T                                 recursive type
          | (tupleType)                                 tuple type
          | {recordType}                                record type
          | <variantType>                               variant type
          | [T]                                         list type

tupleType ::= T, T | T, tupleType
recordType ::= var : T | var : T, recordType
variantType ::= label : T | label : T, variantType
```

module JackParser where

import Control.Monad (liftM, ap, when)
import Data.Char (isDigit, isAlpha, isSpace, ord)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import VMCode

data Class
  = Class String [ClassVar] [Subroutine]
instance Compilable Class where
  compile (Class className classVars subroutines) =
    let
      isStatic (ClassVar scope _) =
        case scope of
          Static -> True
          Field -> False
      toVarDec (ClassVar _ varDec) = varDec
      makeClassScope filterFunction =
        makeScope $
          map toVarDec $
            filter filterFunction classVars
      staticScope = makeClassScope isStatic
      fieldScope = makeClassScope (not . isStatic)
      getName (Subroutine _ _ name _ _ _) = name
      isAMethod (Subroutine funcType _ _ _ _ _) =
        case funcType of
          Method -> True
          _ -> False
      makeFuncSet filterFunction =
        Set.fromList $
          map getName $
            filter filterFunction subroutines
      functionSet = makeFuncSet (not . isAMethod)
      methodSet = makeFuncSet isAMethod
    in
      do
        modifyContext $ \_ ->
          let
            staticContext =
              StaticContextInfo
                { statics = staticScope
                , args = undefined
                , locals = undefined
                , functions = functionSet
                , className
                }
            instanceContext =
              InstanceContextInfo
                { fields = fieldScope
                , methods = methodSet
                }
          in
            Context staticContext (Just instanceContext)
        compileEach subroutines

data Type
  = JackInt
  | JackChar
  | JackBool
  | JackClass String

data ClassVarScope
  = Static
  | Field

data ClassVar
  = ClassVar ClassVarScope VarDec

data SubroutineType
  = Method
  | Constructor
  | Function

data Subroutine
  = Subroutine SubroutineType (Maybe Type) String [Parameter] [VarDec] [Statement]
instance Compilable Subroutine where
  compile (Subroutine funcType _ funcName parameters locals body) = do
    className <- getClass
    fieldCount <- getFieldCount
    constantCompiler
      [
        FunctionInstruction
        (vmFunctionName className funcName)
        (length locals)
      ]
    modifyContext $ \(Context staticContext instanceContext) ->
      let
        implicitParameters = case funcType of
          Method ->
            Parameter (JackClass "Array") "this" : parameters
          _ ->
            parameters
        toVarDec (Parameter jackType name) = VarDec jackType [name]
        newInstanceContext = case funcType of
          Method -> instanceContext
          _ -> Nothing
      in
        Context
          (
            staticContext
              { args =
                makeScope $
                  map toVarDec implicitParameters
              , locals = makeScope locals
              }
          )
          newInstanceContext
    case funcType of
      Method ->
        constantCompiler
          [ PushInstruction (Target ArgumentSegment 0)
          , PopInstruction this
          ]
      Constructor -> do
        compile (IntConst fieldCount)
        constantCompiler
          [ CallInstruction
            (vmFunctionName "Memory" "alloc")
            1
          , PopInstruction this
          ]
      Function ->
        return ()
    compileEach body
    constantCompiler [EmptyInstruction]

data Parameter =
  Parameter Type String

data VarDec =
  VarDec Type [String]

data Statement
  = Let VarAccess Expression
  | If Expression [Statement] [Statement]
  | While Expression [Statement]
  | Do SubCall
  | Return (Maybe Expression)
instance Compilable Statement where
  compile (Let access expression) = do
    compile expression
    target <- compileAccess access
    constantCompiler [PopInstruction target]
  compile (Do subCall) = do
    compile subCall
    constantCompiler
      [PopInstruction (Target TempSegment 0)]
  compile (Return Nothing) = do
    compile $
      Return $
        Just (Expression (IntConst 0) [])
  compile (Return (Just expression)) = do
    compile expression
    constantCompiler [ReturnInstruction]

data VarAccess
  = Var String
  | Subscript String Expression
compileAccess :: VarAccess -> ContextCompiler Target
compileAccess (Var var) = resolveVarTarget var
compileAccess (Subscript var index) = do
  arrayTarget <- resolveVarTarget var
  constantCompiler [PushInstruction arrayTarget]
  compile index
  constantCompiler
    [ AddInstruction
    , PopInstruction that
    ]
  return (Target ThatSegment 0)

data Expression
  = Expression Term [(Op, Term)]
instance Compilable (Op, Term) where
  compile (op, term) = do
    compile term
    compile op
instance Compilable Expression where
  compile (Expression firstTerm opTerms) = do
    compile firstTerm
    compileEach opTerms

data Op
  = Plus
  | Minus
  | Times
  | Div
  | And
  | Or
  | LessThan
  | GreaterThan
  | EqualTo
instance Compilable Op where
  compile Plus = constantCompiler [AddInstruction]
  compile Minus = constantCompiler [SubInstruction]
  compile Times =
    constantCompiler
      [
        CallInstruction
        (vmFunctionName "Math" "multiply")
        2
      ]
  compile Div =
    constantCompiler
      [
        CallInstruction
        (vmFunctionName "Math" "divide")
        2
      ]
  compile And = constantCompiler [AddInstruction]
  compile Or = constantCompiler [OrInstruction]
  compile LessThan = constantCompiler [LessThanInstruction]
  compile GreaterThan = constantCompiler [GreaterThanInstruction]
  compile EqualTo = constantCompiler [EqualsInstruction]

data Term
  = IntConst Int
  | StringConst String
  | Parenthesized Expression
  | BoolConst Bool
  | This
  | Null
  | Access VarAccess
  | SubroutineCall SubCall
  | Unary UnaryOp Term
instance Compilable Term where --compiles into code that pushes value to stack
  compile (IntConst int) =
    constantCompiler
      [PushInstruction (Target ConstantSegment int)]
  compile (StringConst string) = do
    compile (IntConst (length string))
    constantCompiler
      [
        CallInstruction
        (vmFunctionName "String" "new")
        1
      ]
    compileInOrder $
      map
        (compile . IntConst . ord)
        string
  compile (Parenthesized expression) =
    compile expression
  compile (BoolConst False) =
    compile (IntConst 0)
  compile (BoolConst True) = do
    compile (BoolConst False)
    compile LogicalNot
  compile This =
    compile (Access (Var "this"))
  compile Null =
    compile (IntConst 0)
  compile (Access access) = do
    target <- compileAccess access
    constantCompiler [PushInstruction target]
  compile (SubroutineCall subCall) =
    compile subCall
  compile (Unary op term) = do
    compile term
    compile op

data SubCall
  = Unqualified String [Expression]
  | Qualified String String [Expression]
instance Compilable SubCall where --calls the function and leaves the return result at the top of the stack
  compile (Unqualified funcName expressions) = do
    className <- getClass
    method <- isMethod funcName
    when method $ compile This
    compileEach expressions
    let
      explicitArgs = length expressions
      args =
        if method then explicitArgs + 1
        else explicitArgs
    constantCompiler
      [
        CallInstruction
        (vmFunctionName className funcName)
        args
      ]
  compile (Qualified qualifier funcName expressions) = do
    resolvedQualifier <- maybeResolveVar qualifier
    let
      qualifierIsVar =
        case resolvedQualifier of
          Just _ -> True
          Nothing -> False
      explicitArgs = length expressions
    if qualifierIsVar then do
      compile (Access (Var qualifier))
      compileEach expressions
      varClass <- getVarClass qualifier
      constantCompiler
        [
          CallInstruction
          (vmFunctionName varClass funcName)
          (explicitArgs + 1) --include the "this" value in the arg count
        ]
    else do
      compileEach expressions
      constantCompiler
        [
          CallInstruction
          (vmFunctionName qualifier funcName)
          explicitArgs
        ]

data UnaryOp
  = LogicalNot
  | IntegerNegate
instance Compilable UnaryOp where --applies the unary op to the value at the top of the stack
  compile LogicalNot =
    constantCompiler [NotInstruction]
  compile IntegerNegate =
    constantCompiler [NegInstruction]

newtype Parser a = Parser (String -> Maybe (a, String))

parse :: Parser a -> String -> Maybe (a, String)
parse (Parser f) = f

instance Monad Parser where
  (>>=) = parseAndThen
  return = parseReturn
instance Applicative Parser where
  (<*>) = ap
  pure = return
instance Functor Parser where
  fmap = liftM

parseReturn :: a -> Parser a
parseReturn x =
  Parser $ \s -> Just (x, s)

parseAndThen :: Parser a -> (a -> Parser b) -> Parser b
parseAndThen pa f =
  Parser $ \s ->
    case parse pa s of
      Nothing -> Nothing
      Just (a, s') -> parse (f a) s'

satisfies :: (Char -> Bool) -> Parser Char
satisfies c =
  Parser $ \s ->
    case s of
      [] ->
        Nothing
      first : rest ->
        if c first then
          Just (first, rest)
        else
          Nothing

keyword :: String -> Parser ()
keyword "" = return ()
keyword (c : cs) = do
  _ <- satisfies (c ==)
  keyword cs

parseMap :: (a -> b) -> Parser a -> Parser b
parseMap aToB pa = parseMap2 (const . aToB) pa (return ())

parseMap2 :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
parseMap2 f pa pb = do
  a <- pa
  b <- pb
  return (f a b)

parseKeywordValue :: [(String, a)] -> Parser a
parseKeywordValue nameValues =
  let
    getParser (name, value) =
      parseMap (const value) (keyword name)
  in
    choice (map getParser nameValues)

parseClassVarScope :: Parser ClassVarScope
parseClassVarScope =
  parseKeywordValue
    [ ("static", Static)
    , ("field", Field)
    ]

zeroOrMore :: Parser a -> Parser [a]
zeroOrMore parser =
  Parser $ \string ->
    case parse parser string of
      Nothing ->
        Just ([], string)
      Just (aValue, remaining) ->
        parse (parseMap (aValue :) (zeroOrMore parser)) remaining

oneOrMore :: Parser a -> Parser [a]
oneOrMore parser = parseMap2 (:) parser (zeroOrMore parser)

identifier :: Parser String
identifier =
  let
    isValidFirstChar c =
      isAlpha c || c == '_'
    isValidLaterChar c =
      isValidFirstChar c || isDigit c
  in
    parseMap2 (:) (satisfies isValidFirstChar) (zeroOrMore (satisfies isValidLaterChar))

jackTypeParser :: Parser Type
jackTypeParser =
  choice
    [ parseKeywordValue
      [ ("int", JackInt)
      , ("char", JackChar)
      , ("boolean", JackBool)
      ]
    , parseMap JackClass identifier
    ]

choice :: [Parser a] -> Parser a
choice [] = parseFail
choice (firstChoice : remainingChoices) =
  Parser $ \string ->
    case parse firstChoice string of
      Nothing ->
        parse (choice remainingChoices) string
      success ->
        success

parseUntil :: Parser a -> Parser a
parseUntil parser =
  Parser $ \string ->
    let parsed = parse parser string
    in
      case parsed of
        Nothing ->
          case string of
            "" ->
              Nothing
            _ : remaining ->
              parse (parseUntil parser) remaining
        _ ->
          parsed

parseEnd :: Parser ()
parseEnd =
  Parser $ \string ->
    case string of
      "" -> Just ((), "")
      _ -> Nothing

isNewLine :: Char -> Bool
isNewLine c = c == '\r' || c == '\n'

parseLineComment :: Parser ()
parseLineComment = do
  keyword "//"
  parseUntil $ choice
    [ parseMap (const ()) (satisfies isNewLine)
    , parseEnd
    ]

parseBlockComment :: Parser ()
parseBlockComment = do
  keyword "/*"
  parseUntil (keyword "*/")

whiteSpaceParser :: Parser ()
whiteSpaceParser =
  Parser $ \string ->
    let dropped = dropWhile isSpace string
    in
      if string == dropped then Nothing -- some whitespace required
      else Just ((), dropped)

requiredSpaceParser :: Parser ()
requiredSpaceParser = do
  _ <- oneOrMore $ choice
    [ whiteSpaceParser
    , parseLineComment
    , parseBlockComment
    ]
  return ()

optionalSpaceParser :: Parser ()
optionalSpaceParser = do
  _ <- parseOptional requiredSpaceParser
  return ()

parseCommaSeparated :: Parser a -> Parser [a]
parseCommaSeparated parser = do
  first <- parser
  remaining <- zeroOrMore $ do
    optionalSpaceParser
    keyword ","
    optionalSpaceParser
    parser
  return (first : remaining)

optionalParseCommaSeparated :: Parser a -> Parser [a]
optionalParseCommaSeparated parser =
  parseMap resolveMaybeList $
    parseOptional $
      parseCommaSeparated parser

parseFail :: Parser a
parseFail = Parser (const Nothing)

parseVarDec :: Parser VarDec
parseVarDec = do
  jackType <- jackTypeParser
  requiredSpaceParser
  vars <- parseCommaSeparated identifier
  optionalSpaceParser
  keyword ";"
  return (VarDec jackType vars)

parseClassVar :: Parser ClassVar
parseClassVar = do
  scope <- parseClassVarScope
  requiredSpaceParser
  dec <- parseVarDec
  return (ClassVar scope dec)

parseOptional :: Parser a -> Parser (Maybe a)
parseOptional parser =
  choice
    [ parseMap Just parser
    , return Nothing
    ]

parseIntConstant :: Parser Int
parseIntConstant =
  Parser $ \string ->
    case string of
      "" ->
        Nothing
      firstChar : _ ->
        if isDigit firstChar then
          Just (read (takeWhile isDigit string), dropWhile isDigit string)
        else Nothing

parseShort :: Parser Term
parseShort = do
  int <- parseIntConstant
  if int <= 32767 then return (IntConst int)
  else parseFail

parseStringConstant :: Parser Term
parseStringConstant = do
  keyword "\""
  string <- zeroOrMore $
    satisfies $ \c ->
      not ((isNewLine c) || c == '"')
  keyword "\""
  return (StringConst string)

parseSubscript :: Parser VarAccess
parseSubscript = do
  varName <- identifier
  optionalSpaceParser
  keyword "["
  optionalSpaceParser
  index <- parseExpression
  optionalSpaceParser
  keyword "]"
  return (Subscript varName index)

parseAccess :: Parser VarAccess
parseAccess =
  choice
    [ parseSubscript
    , parseMap Var identifier -- this must come after array access because it can start that expression
    ]

parseParenthesized :: Parser Term
parseParenthesized = do
  keyword "("
  optionalSpaceParser
  expression <- parseExpression
  optionalSpaceParser
  keyword ")"
  return (Parenthesized expression)

parseUnqualifiedSubCall :: Parser SubCall
parseUnqualifiedSubCall = do
  name <- identifier
  optionalSpaceParser
  keyword "("
  optionalSpaceParser
  arguments <- optionalParseCommaSeparated parseExpression
  optionalSpaceParser
  keyword ")"
  return (Unqualified name arguments)

parseQualifiedSubCall :: Parser SubCall
parseQualifiedSubCall = do
  classOrVarName <- identifier
  optionalSpaceParser
  keyword "."
  optionalSpaceParser
  Unqualified callName arguments <- parseUnqualifiedSubCall
  return (Qualified classOrVarName callName arguments)

parseSubCall :: Parser SubCall
parseSubCall =
  choice
    [ parseUnqualifiedSubCall
    , parseQualifiedSubCall
    ]

parseUnaryOp :: Parser UnaryOp
parseUnaryOp =
  parseKeywordValue
    [ ("~", LogicalNot)
    , ("-", IntegerNegate)
    ]

parseUnaryOperation :: Parser Term
parseUnaryOperation = do
  op <- parseUnaryOp
  optionalSpaceParser
  term <- parseTerm
  return (Unary op term)

parseTerm :: Parser Term
parseTerm =
  choice
    [ parseShort
    , parseStringConstant
    , parseKeywordValue
      [ ("true", BoolConst True)
      , ("false", BoolConst False)
      , ("null", Null)
      , ("this", This)
      ]
    , parseMap SubroutineCall parseSubCall
    , parseMap Access parseAccess -- this must come after array subroutine call because a variable access can start that expression
    , parseParenthesized
    , parseUnaryOperation
    ]

parseOp :: Parser Op
parseOp =
  parseKeywordValue
    [ ("+", Plus)
    , ("-", Minus)
    , ("*", Times)
    , ("/", Div)
    , ("&", And)
    , ("|", Or)
    , ("<", LessThan)
    , (">", GreaterThan)
    , ("=", EqualTo)
    ]

parseExpression :: Parser Expression
parseExpression =
  parseMap2 Expression parseTerm $
    zeroOrMore $ do
      optionalSpaceParser
      op <- parseOp
      optionalSpaceParser
      term <- parseTerm
      return (op, term)

parseLet :: Parser Statement
parseLet = do
  keyword "let"
  requiredSpaceParser
  access <- parseAccess
  optionalSpaceParser
  keyword "="
  optionalSpaceParser
  expression <- parseExpression
  optionalSpaceParser
  keyword ";"
  return (Let access expression)

-- Parses a list of statements, including surrounding whitespace
parseBlock :: Parser [Statement]
parseBlock = do
  optionalSpaceParser
  zeroOrMore $ do
    statement <- parseStatement
    optionalSpaceParser
    return statement

parseConditionAndBlock :: String -> Parser (Expression, [Statement])
parseConditionAndBlock controlKeyword = do
  keyword controlKeyword
  optionalSpaceParser
  keyword "("
  optionalSpaceParser
  expression <- parseExpression
  optionalSpaceParser
  keyword ")"
  optionalSpaceParser
  keyword "{"
  block <- parseBlock
  keyword "}"
  return (expression, block)

parseElse :: Parser [Statement]
parseElse = do
  keyword "else"
  optionalSpaceParser
  keyword "{"
  block <- parseBlock
  keyword "}"
  return block

resolveMaybeList :: Maybe [a] -> [a]
resolveMaybeList Nothing = []
resolveMaybeList (Just as) = as

parseIf :: Parser Statement
parseIf = do
  (expression, block) <- parseConditionAndBlock "if"
  optionalSpaceParser
  elseBlock <- parseMap resolveMaybeList $
    parseOptional parseElse
  return (If expression block elseBlock)

parseWhile :: Parser Statement
parseWhile = do
  (expression, block) <- parseConditionAndBlock "while"
  return (While expression block)

parseDo :: Parser Statement
parseDo = do
  keyword "do"
  requiredSpaceParser
  subCall <- parseSubCall
  optionalSpaceParser
  keyword ";"
  return (Do subCall)

parseReturnStatement :: Parser Statement
parseReturnStatement =
  let
    spaceAndValueParser = do
      requiredSpaceParser
      expression <- parseExpression
      optionalSpaceParser
      return (Just expression)
  in
    do
      keyword "return"
      returnValue <- choice
        [ spaceAndValueParser
        , parseMap (const Nothing) optionalSpaceParser -- this must come after the return value parser since "return" is at the start of "return value"
        ]
      keyword ";"
      return (Return returnValue)

parseStatement :: Parser Statement
parseStatement =
  choice
    [ parseLet
    , parseIf
    , parseWhile
    , parseDo
    , parseReturnStatement
    ]

parseSubroutineType :: Parser SubroutineType
parseSubroutineType =
  parseKeywordValue
    [ ("method", Method)
    , ("constructor", Constructor)
    , ("function", Function)
    ]

parseMaybeVoidType :: Parser (Maybe Type)
parseMaybeVoidType =
  choice
    [ parseKeywordValue [("void", Nothing)]
    , parseMap Just jackTypeParser
    ]

parseParameter :: Parser Parameter
parseParameter = do
  jackType <- jackTypeParser
  requiredSpaceParser
  name <- identifier
  return (Parameter jackType name)

parseSubroutine :: Parser Subroutine
parseSubroutine = do
  methodType <- parseSubroutineType
  requiredSpaceParser
  returnType <- parseMaybeVoidType
  requiredSpaceParser
  name <- identifier
  optionalSpaceParser
  keyword "("
  optionalSpaceParser
  parameters <- optionalParseCommaSeparated parseParameter
  keyword ")"
  optionalSpaceParser
  keyword "{"
  variables <- zeroOrMore $ do
    optionalSpaceParser
    keyword "var"
    requiredSpaceParser
    parseVarDec
  statements <- parseBlock
  keyword "}"
  return (Subroutine methodType returnType name parameters variables statements)

parseClass :: Parser Class
parseClass = do
  optionalSpaceParser -- must include surrounding whitespace because this is the root parser
  keyword "class"
  requiredSpaceParser
  name <- identifier
  optionalSpaceParser
  keyword "{"
  varDecs <- zeroOrMore $ do
    optionalSpaceParser
    parseClassVar
  subroutines <- zeroOrMore $ do
    optionalSpaceParser
    parseSubroutine
  optionalSpaceParser
  keyword "}"
  return (Class name varDecs subroutines)

type Scope = Map.Map String (Type, Int)
type FuncSet = Set.Set String
data StaticContextInfo = StaticContextInfo
  {statics :: Scope, args :: Scope, locals :: Scope, functions :: FuncSet, className :: String}
data InstanceContextInfo = InstanceContextInfo {fields :: Scope, methods :: FuncSet}
data Context
  = Context StaticContextInfo (Maybe InstanceContextInfo)

makeScope :: [VarDec] -> Scope
makeScope varDecs =
  let
    enumerate = zip [(0 :: Int)..] --taken from http://stackoverflow.com/a/6473153
    mapWithIndex f xs = map f (enumerate xs)
    singleVars (VarDec jackType vars) =
      map (\var -> (var, jackType)) vars
  in
    Map.fromList $
      mapWithIndex
        (\(index, (var, jackType)) -> (var, (jackType, index))) $
          concat $
            map singleVars varDecs

maybeResolveVar :: String -> ContextCompiler (Maybe (Type, Target))
maybeResolveVar varName =
  let
    lookupStatic var (StaticContextInfo {statics, args, locals}) =
      case Map.lookup var locals of
        Just (jackType, offset) ->
          Just (jackType, Target LocalSegment offset)
        Nothing ->
          case Map.lookup var args of
            Just (jackType, offset) ->
              Just (jackType, Target ArgumentSegment offset)
            Nothing ->
              case Map.lookup var statics of
                Just (jackType, offset) ->
                  Just (jackType, Target StaticSegment offset)
                Nothing ->
                  Nothing
  in
    ContextCompiler $ \context ->
      let
        Context staticContext instanceContext = context
        resolvedVar =
          case lookupStatic varName staticContext of
            Nothing ->
              case instanceContext of
                Nothing ->
                  Nothing
                Just (InstanceContextInfo {fields}) ->
                  case Map.lookup varName fields of
                    Just (jackType, offset) ->
                      Just (jackType, Target ThisSegment offset)
                    Nothing ->
                      Nothing
            result ->
              result
      in
        ([], context, resolvedVar)

resolveVar :: String -> ContextCompiler (Type, Target)
resolveVar var = do
  maybeResult <- maybeResolveVar var
  case maybeResult of
    Just result -> return result
    Nothing -> error ("Could not resolve variable: " ++ var)

resolveVarTarget :: String -> ContextCompiler Target
resolveVarTarget var = do
  (_, target) <- resolveVar var
  return target

isMethod :: String -> ContextCompiler Bool
isMethod funcName =
  ContextCompiler $ \context ->
    let
      noFunctionError = error ("No such function/method: " ++ funcName)
      (Context (StaticContextInfo {functions}) instanceContext) = context
      method =
        if Set.member funcName functions then
          False
        else
          case instanceContext of
            Nothing ->
              noFunctionError
            Just (InstanceContextInfo {methods}) ->
              if Set.member funcName methods then
                True
              else
                noFunctionError
    in
      ([], context, method)

getClass :: ContextCompiler String
getClass =
  ContextCompiler $ \context ->
      let
        Context (StaticContextInfo {className}) _ = context
      in
        ([], context, className)

getVarClass :: String -> ContextCompiler String
getVarClass var = do
  (varType, _) <- resolveVar var
  case varType of
    JackClass className -> return className
    _ -> error ("Cannot call method on primitive: " ++ var)

getFieldCount :: ContextCompiler Int
getFieldCount =
  ContextCompiler $ \context ->
    let Context _ instanceContext = context
    in
      case instanceContext of
        Just (InstanceContextInfo {fields}) ->
          ([], context, Map.size fields)
        Nothing ->
          error "Can't count fields on static function"

vmFunctionName :: String -> String -> String
vmFunctionName className funcName =
  className ++ "." ++ funcName

newtype ContextCompiler a = ContextCompiler (Context -> ([VMInstruction], Context, a))
compileInContext :: ContextCompiler a -> Context -> ([VMInstruction], Context, a)
compileInContext (ContextCompiler compiler) = compiler
executeRootCompiler :: (Compilable a) => a -> [VMInstruction]
executeRootCompiler compilable =
  let
    compiler = compile compilable
    emptyContext =
      Context
        (
          StaticContextInfo
            { statics = undefined
            , args = undefined
            , locals = undefined
            , functions = undefined
            , className = undefined
            }
        )
        Nothing
    (instructions, _, _) = compileInContext compiler emptyContext
  in
    instructions

instance Monad ContextCompiler where
  compilerA >>= aToCompilerB =
    ContextCompiler $ \context ->
      let
        (instructions, context', a) = compileInContext compilerA context
        compilerB = aToCompilerB a
        (instructions', context'', b) = compileInContext compilerB context'
      in
        (instructions ++ instructions', context'', b)
  return a = ContextCompiler $ \context -> ([], context, a)
instance Applicative ContextCompiler where
  (<*>) = ap
  pure = return
instance Functor ContextCompiler where
  fmap = liftM

modifyContext :: (Context -> Context) -> ContextCompiler ()
modifyContext modify =
  ContextCompiler $ \context -> ([], modify context, ())
constantCompiler :: [VMInstruction] -> ContextCompiler ()
constantCompiler instructions =
  ContextCompiler $ \context ->
    (instructions, context, ())
compileInOrder :: [ContextCompiler ()] -> ContextCompiler ()
compileInOrder [] = constantCompiler []
compileInOrder (compiler : compilers) = do
  compiler
  compileInOrder compilers
compileEach :: (Compilable a) => [a] -> ContextCompiler ()
compileEach = compileInOrder . map compile

class Compilable a where
  compile :: a -> ContextCompiler ()
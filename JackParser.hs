module JackParser where

import Control.Monad (liftM, ap)
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
      isMethod (Subroutine funcType _ _ _ _ _) =
        case funcType of
          Method -> True
          _ -> False
      makeFuncSet filterFunction =
        Set.fromList $
          map getName $
            filter filterFunction subroutines
      functionSet = makeFuncSet (not . isMethod)
      methodSet = makeFuncSet isMethod
    in
      concat $
        map
          (compileSubroutine className staticScope fieldScope functionSet methodSet)
          subroutines

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
compileSubroutine ::
  String ->
  Scope ->
  Scope ->
  FuncSet ->
  FuncSet ->
    Subroutine -> [VMInstruction]
compileSubroutine className staticScope fieldScope functionSet methodSet subroutine =
  let
    Subroutine funcType _ funcName parameters locals body = subroutine --it doesn't matter what type the function returns
    initialization = case funcType of
      Method -> --put first argument into this
        [ PushInstruction (Target ArgumentSegment 0)
        , PopInstruction this
        ]
      Constructor -> --allocate memory, set this variable
        compileInContext context (IntConst (Map.size fieldScope)) ++
        [ CallInstruction
          (vmFunctionName "Memory" "alloc")
          1
        , PopInstruction this
        ]
      Function ->
        []
    toVarDec (Parameter jackType name) = VarDec jackType [name]
    implicitParameters = case funcType of
      Method ->
        Parameter (JackClass "Array") "this" : parameters
      _ ->
        parameters
    staticContext = StaticContextInfo
      { statics = staticScope
      , args =
        makeScope $
          map toVarDec implicitParameters
      , locals =
        makeScope locals
      , functions = functionSet
      , className
      }
    context = case funcType of
      Method ->
        InstanceContext
          { staticContext
          , fields = fieldScope
          , methods = methodSet
          }
      _ ->
        StaticContext staticContext
  in
    [
      FunctionInstruction
      (vmFunctionName className funcName)
      (length locals)
    ] ++
    initialization ++
    compileInContext context body

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
instance ContextCompilable Statement where
  compileInContext context (Let access expression) =
    let
      (accessInstructions, target) = computeTarget access context
    in
      compileInContext context expression ++
      accessInstructions ++
      [PopInstruction target]
  compileInContext context (Do subCall) =
    compileInContext context subCall ++
    [PopInstruction (Target TempSegment 0)]
  compileInContext context (Return Nothing) =
    compileInContext context $
      Return $
        Just (Expression (IntConst 0) [])
  compileInContext context (Return (Just expression)) =
    compileInContext context expression ++
    [ReturnInstruction]

data VarAccess
  = Var String
  | Subscript String Expression
computeTarget :: VarAccess -> Context -> ([VMInstruction], Target)
computeTarget (Var var) context =
  ([], resolveVarTarget context var)
computeTarget (Subscript var index) context =
  let
    arrayTarget = resolveVarTarget context var
    instructions =
      [PushInstruction arrayTarget] ++
      compileInContext context index ++
      [ AddInstruction
      , PopInstruction that
      ]
  in
    (instructions, Target ThatSegment 0)

data Expression
  = Expression Term [(Op, Term)]
instance ContextCompilable Expression where
  compileInContext context (Expression firstTerm opTerms) =
    compileInContext context firstTerm ++
    (
      concat $
        map
          (\(op, term) -> compileInContext context term ++ compile op)
          opTerms
    )

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
  compile Plus = [AddInstruction]
  compile Minus = [SubInstruction]
  compile Times =
    [
      CallInstruction
      (vmFunctionName "Math" "multiply")
      2
    ]
  compile Div =
    [
      CallInstruction
      (vmFunctionName "Math" "divide")
      2
    ]
  compile And = [AddInstruction]
  compile Or = [OrInstruction]
  compile LessThan = [LessThanInstruction]
  compile GreaterThan = [GreaterThanInstruction]
  compile EqualTo = [EqualsInstruction]

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
instance ContextCompilable Term where --compiles into code that pushes value to stack
  compileInContext _ (IntConst int) =
    [PushInstruction (Target ConstantSegment int)]
  compileInContext context (StringConst string) =
    compileInContext context (IntConst (length string)) ++
    [
      CallInstruction
      (vmFunctionName "String" "new")
      1
    ] ++
    (
      concat $
        map
          (compileInContext context . IntConst . ord)
          string
    )
  compileInContext context (Parenthesized expression) =
    compileInContext context expression
  compileInContext context (BoolConst False) =
    compileInContext context (IntConst 0)
  compileInContext context (BoolConst True) =
    compileInContext context (BoolConst False) ++
    [NotInstruction]
  compileInContext context This =
    compileInContext context (Access (Var "this"))
  compileInContext context Null =
    compileInContext context (IntConst 0)
  compileInContext context (Access access) =
    let
      (accessInstructions, target) = computeTarget access context
    in
      accessInstructions ++ [PushInstruction target]
  compileInContext context (SubroutineCall subCall) =
    compileInContext context subCall
  compileInContext context (Unary op term) =
    compileInContext context term ++ compile op

data SubCall
  = Unqualified String [Expression]
  | Qualified String String [Expression]
instance ContextCompilable SubCall where --calls the function and leaves the return result at the top of the stack
  compileInContext context (Unqualified funcName expressions) =
    let
      pushExpressions = compileInContext context expressions
      (pushThis, args) =
        if isFunction context funcName then
          ([], length expressions)
        else
          (compileInContext context This, length expressions + 1)
    in
      pushThis ++
      pushExpressions ++
      [
        CallInstruction
        (vmFunctionName (getClass context) funcName)
        args
      ]
  compileInContext context (Qualified qualifier funcName expressions) =
    let
      qualifierIsClass =
        case maybeResolveVar context qualifier of
          Nothing -> True
          Just _ -> False
      pushExpressions = compileInContext context expressions
      explicitArgs = length expressions
    in
      if qualifierIsClass then
        pushExpressions ++
        [
          CallInstruction
          (vmFunctionName qualifier funcName)
          explicitArgs
        ]
      else --qualifier is a variable
        compileInContext context (Access (Var qualifier)) ++
        pushExpressions ++
        [
          CallInstruction
          (vmFunctionName (getVarClass context qualifier) funcName)
          (explicitArgs + 1) --include the "this" value in the arg count
        ]

data UnaryOp
  = LogicalNot
  | IntegerNegate
instance Compilable UnaryOp where --applies the unary op to the value at the top of the stack
  compile LogicalNot = [NotInstruction]
  compile IntegerNegate = [NegInstruction]

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
data Context
  = StaticContext StaticContextInfo
  | InstanceContext
    {staticContext :: StaticContextInfo, fields :: Scope, methods :: FuncSet}

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

maybeResolveVar :: Context -> String -> Maybe (Type, Target)
maybeResolveVar (StaticContext (StaticContextInfo {statics, args, locals})) var =
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
maybeResolveVar (InstanceContext {staticContext, fields}) var =
  case maybeResolveVar (StaticContext staticContext) var of
    Nothing ->
      case Map.lookup var fields of
        Just (jackType, offset) ->
          Just (jackType, Target ThisSegment offset)
        Nothing ->
          Nothing
    target ->
      target

resolveVar :: Context -> String -> (Type, Target)
resolveVar context var =
  case maybeResolveVar context var of
    Just result -> result
    Nothing -> error ("Could not resolve variable: " ++ var)

resolveVarTarget :: Context -> String -> Target
resolveVarTarget context var =
  let (_, target) = resolveVar context var
  in target

isFunction :: Context -> String -> Bool
isFunction (StaticContext (StaticContextInfo {functions})) funcName =
  if Set.member funcName functions then
    True
  else
    error ("No such function/method: " ++ funcName)
isFunction (InstanceContext {staticContext, methods}) funcName =
  if Set.member funcName methods then
    False
  else
    isFunction (StaticContext staticContext) funcName

getClass :: Context -> String
getClass (StaticContext (StaticContextInfo {className})) = className
getClass (InstanceContext {staticContext}) =
  getClass (StaticContext staticContext)

getVarClass :: Context -> String -> String
getVarClass context var =
  let (varType, _) = resolveVar context var
  in
    case varType of
      JackClass className -> className
      _ -> error ("Cannot call method on primitive: " ++ var)

vmFunctionName :: String -> String -> String
vmFunctionName className funcName =
  className ++ "." ++ funcName

type Compilation a = a -> [VMInstruction]
class Compilable a where
  compile :: Compilation a
class ContextCompilable a where
  compileInContext :: Context -> Compilation a
instance (ContextCompilable a) => ContextCompilable [a] where
  compileInContext context =
    concat . map (compileInContext context)
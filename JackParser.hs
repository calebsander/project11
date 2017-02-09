module JackParser where

import Control.Monad (liftM, ap)
import Data.Char (isDigit, isAlpha, isSpace)

data Class
  = Class String [ClassVar] [Subroutine]

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

data VarAccess
  = Var String
  | Subscript String Expression

data Expression
  = Expression Term [(Op, Term)]

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

data SubCall
  = Unqualified String [Expression]
  | Qualified String String [Expression]

data UnaryOp
  = LogicalNot
  | IntegerNegate

newtype Parser a = Parser (String -> Maybe (a, String))

parse :: Parser a -> String -> Maybe (a, String)
parse (Parser f) = f

instance Monad Parser where
  pa >>= f =
    Parser $ \s ->
      case parse pa s of
        Nothing -> Nothing
        Just (a, s') -> parse (f a) s'
  return x = Parser $ \s -> Just (x, s)
instance Applicative Parser where
  (<*>) = ap
  pure = return
instance Functor Parser where
  fmap = liftM

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

parseMap2 :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
parseMap2 f pa pb = do
  a <- pa
  b <- pb
  return (f a b)

parseKeywordValue :: [(String, a)] -> Parser a
parseKeywordValue nameValues =
  let
    getParser (name, value) =
      fmap (const value) (keyword name)
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
        parse (fmap (aValue :) (zeroOrMore parser)) remaining

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
    , fmap JackClass identifier
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
    [ fmap (const ()) (satisfies isNewLine)
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
  fmap resolveMaybeList $
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
    [ fmap Just parser
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
    , fmap Var identifier -- this must come after array access because it can start that expression
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
    , fmap SubroutineCall parseSubCall
    , fmap Access parseAccess -- this must come after array subroutine call because a variable access can start that expression
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
  elseBlock <- fmap resolveMaybeList $
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
        , fmap (const Nothing) optionalSpaceParser -- this must come after the return value parser since "return" is at the start of "return value"
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
    , fmap Just jackTypeParser
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
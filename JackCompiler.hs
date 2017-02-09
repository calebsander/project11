module JackCompiler where

import Control.Monad (liftM, ap, when)
import Data.Char (ord)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import JackParser
import VMCode

type Scope = Map.Map String (Type, Int)

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

type FuncSet = Set.Set String
data StaticContextInfo = StaticContextInfo
  {statics :: Scope, args :: Scope, locals :: Scope, functions :: FuncSet, className :: String}
data InstanceContextInfo = InstanceContextInfo {fields :: Scope, methods :: FuncSet}
data Context
  = Context StaticContextInfo (Maybe InstanceContextInfo)

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
      classContext = Context staticContext (Just instanceContext)
    in
      do
        modifyContext (const classContext)
        compileEach subroutines

instance Compilable Subroutine where
  compile (Subroutine funcType _ funcName parameters locals statements) = do
    className <- getClass
    fieldCount <- getFieldCount --have to count fields (for constructor) before modifying context to hide instanceContext
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
      Method -> --set this to arg 0
        constantCompiler
          [ PushInstruction (Target ArgumentSegment 0)
          , PopInstruction this
          ]
      Constructor -> do --allocate memory for this
        compile (IntConst fieldCount)
        constantCompiler
          [ CallInstruction
            (vmFunctionName "Memory" "alloc")
            1
          , PopInstruction this
          ]
      Function ->
        return ()
    compileEach statements
    constantCompiler [EmptyInstruction] --for readability

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
    compile (IntConst 0)
    constantCompiler [ReturnInstruction]
  compile (Return (Just expression)) = do
    compile expression
    constantCompiler [ReturnInstruction]

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

instance Compilable (Op, Term) where
  compile (op, term) = do
    compile term
    compile op
instance Compilable Expression where
  compile (Expression firstTerm opTerms) = do
    compile firstTerm
    compileEach opTerms

instance Compilable Op where --compiles into code that calls op on top 2 stack values
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

instance Compilable SubCall where --compiles into code that calls the function and leaves the return result at the top of the stack
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

instance Compilable UnaryOp where --compiles into code that calls op on top stack value
  compile LogicalNot =
    constantCompiler [NotInstruction]
  compile IntegerNegate =
    constantCompiler [NegInstruction]
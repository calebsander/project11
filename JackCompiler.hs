module JackCompiler where

import Control.Monad (liftM, ap, when)
import Data.Char (ord)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import JackParser
import VMCode

type Scope = Map.Map String (Type, Int)

singleVars :: [VarDec] -> [(String, Type)]
singleVars =
  concat .
  map
    (
      \(VarDec jackType vars) ->
        map (\var -> (var, jackType)) vars
    )

makeScope :: [VarDec] -> Scope
makeScope varDecs =
  let
    enumerate = zip [(0 :: Int)..] --taken from http://stackoverflow.com/a/6473153
    mapWithIndex f xs = map f (enumerate xs)
  in
    Map.fromList $
      mapWithIndex
        (\(index, (var, jackType)) -> (var, (jackType, index))) $
          singleVars varDecs

type FuncSet = Set.Set String
data StaticContextInfo = StaticContextInfo --every function has a class context and a function context
  {statics :: Scope, args :: Scope, locals :: Scope, functions :: FuncSet, className :: String, minLabelId :: Int}
data InstanceContextInfo = --methods also have an instance context
  InstanceContextInfo {fields :: Scope, methods :: FuncSet}
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
      Context (StaticContextInfo {functions}) instanceContext = context
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

getLabelId :: ContextCompiler String
getLabelId =
  ContextCompiler $ \(Context staticContext instanceContext) ->
    let
      StaticContextInfo {minLabelId} = staticContext
      newContext =
        Context
        (staticContext {minLabelId = minLabelId + 1})
        instanceContext
    in
      ([], newContext, show minLabelId)

getContext :: ContextCompiler Context
getContext =
  ContextCompiler $ \context ->
    ([], context, context)

vmFunctionName :: String -> String -> String
vmFunctionName className funcName =
  className ++ "." ++ funcName

newtype ContextCompiler a = ContextCompiler (Context -> ([VMInstruction], Context, a))
compileInContext :: ContextCompiler a -> Context -> ([VMInstruction], Context, a)
compileInContext (ContextCompiler compiler) = compiler
rootCompile :: (Compilable a) => a -> [VMInstruction]
rootCompile compilable =
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
            , minLabelId = undefined
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
instance Compilable VMInstruction where
  compile instruction =
    ContextCompiler $ \context ->
      ([instruction], context, ())
compileEach :: (Compilable a) => [a] -> ContextCompiler ()
compileEach = sequence_ . map compile

class Compilable a where
  compile :: a -> ContextCompiler ()

instance (Compilable a) => Compilable [a] where
  compile = compileEach

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
          , minLabelId = undefined
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
        compile subroutines

instance Compilable Subroutine where
  compile (Subroutine funcType _ funcName parameters locals body) = do
    className <- getClass
    compile $
      FunctionInstruction
        (vmFunctionName className funcName)
        (length (singleVars locals))
    context <- getContext --save context so it can be restored after this subroutine
    modifyContext $ \(Context staticContext instanceContext) ->
      let
        implicitParameters = case funcType of
          Function ->
            parameters
          _ -> --constructors and methods can access "this"
            Parameter (JackClass "Array") "this" : parameters
        toVarDec (Parameter jackType name) = VarDec jackType [name]
        newInstanceContext = case funcType of
          Function -> Nothing
          _ -> instanceContext --constructors and methods can access the instance
      in
        Context
          (
            staticContext
              { args =
                makeScope $
                  map toVarDec implicitParameters
              , locals = makeScope locals
              , minLabelId = 0
              }
          )
          newInstanceContext
    case funcType of
      Method -> do --set this to arg 0
        compile $
          PushInstruction (Target ArgumentSegment 0)
        compile (PopInstruction this)
      Constructor -> do --allocate memory for this
        fieldCount <- getFieldCount
        compile (IntConst fieldCount)
        compile $
          CallInstruction
            (vmFunctionName "Memory" "alloc")
            1
        compile (PopInstruction this)
      Function ->
        return ()
    compile body
    compile EmptyInstruction --for readability
    modifyContext (const context) --restore context for next subroutine

instance Compilable Statement where
  compile (Let access expression) = do
    compile expression
    target <- compileAccess access
    compile (PopInstruction target)
  compile (If condition ifBlock []) = do --more efficient version if there are no else conditions
    endLabel <- fmap ("IF_END_" ++) getLabelId
    compile (Unary LogicalNot (Parenthesized condition))
    compile (IfGotoInstruction endLabel)
    compile ifBlock
    compile (LabelInstruction endLabel)
  compile (If condition ifBlock elseBlock) = do
    elseLabel <- fmap ("ELSE_" ++) getLabelId
    endLabel <- fmap ("IF_END_" ++) getLabelId
    compile (Unary LogicalNot (Parenthesized condition))
    compile (IfGotoInstruction elseLabel)
    compile ifBlock
    compile (GotoInstruction endLabel)
    compile (LabelInstruction elseLabel)
    compile elseBlock
    compile (LabelInstruction endLabel)
  compile (While condition statements) = do
    startLabel <- fmap ("WHILE_START_" ++) getLabelId
    endLabel <- fmap ("WHILE_END_" ++) getLabelId
    compile (LabelInstruction startLabel)
    compile (Unary LogicalNot (Parenthesized condition))
    compile (IfGotoInstruction endLabel)
    compile statements
    compile (GotoInstruction startLabel)
    compile (LabelInstruction endLabel)
  compile (Do subCall) = do
    compile subCall
    compile $
      PopInstruction (Target TempSegment 0)
  compile (Return Nothing) = do
    compile (IntConst 0)
    compile ReturnInstruction
  compile (Return (Just expression)) = do
    compile expression
    compile ReturnInstruction

compileAccess :: VarAccess -> ContextCompiler Target
compileAccess (Var var) = resolveVarTarget var
compileAccess (Subscript var index) = do
  arrayTarget <- resolveVarTarget var
  compile (PushInstruction arrayTarget)
  compile index
  compile AddInstruction
  compile (PopInstruction that)
  return (Target ThatSegment 0)

instance Compilable (Op, Term) where
  compile (op, term) = do
    compile term
    compile op
instance Compilable Expression where
  compile (Expression firstTerm opTerms) = do
    compile firstTerm
    compile opTerms

instance Compilable Op where --compiles into code that calls op on top 2 stack values
  compile Plus = compile AddInstruction
  compile Minus = compile SubInstruction
  compile Times =
    compile $
      CallInstruction
        (vmFunctionName "Math" "multiply")
        2
  compile Div =
    compile $
      CallInstruction
        (vmFunctionName "Math" "divide")
        2
  compile And = compile AddInstruction
  compile Or = compile OrInstruction
  compile LessThan = compile LessThanInstruction
  compile GreaterThan = compile GreaterThanInstruction
  compile EqualTo = compile EqualsInstruction

instance Compilable Term where --compiles into code that pushes value to stack
  compile (IntConst int) =
    compile $
      PushInstruction (Target ConstantSegment int)
  compile (StringConst string) = do
    compile (IntConst (length string))
    compile $
      CallInstruction
        (vmFunctionName "String" "new")
        1
    sequence_ $
      map
        (
          \c -> do
            compile (IntConst (ord c))
            compile $
              CallInstruction
                (vmFunctionName "String" "appendChar")
                2 --the string and the character
        )
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
    compile (PushInstruction target)
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
    compile expressions
    let
      explicitArgs = length expressions
      args =
        if method then explicitArgs + 1
        else explicitArgs
    compile $
      CallInstruction
        (vmFunctionName className funcName)
        args
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
      compile expressions
      varClass <- getVarClass qualifier
      compile $
        CallInstruction
          (vmFunctionName varClass funcName)
          (explicitArgs + 1) --include the "this" value in the arg count
    else do
      compile expressions
      compile $
        CallInstruction
          (vmFunctionName qualifier funcName)
          explicitArgs

instance Compilable UnaryOp where --compiles into code that calls op on top stack value
  compile LogicalNot = compile (NotInstruction)
  compile IntegerNegate = compile (NegInstruction)
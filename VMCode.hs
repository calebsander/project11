module VMCode where

import Data.List (intercalate)

data Segment
  = ArgumentSegment
  | ConstantSegment
  | LocalSegment
  | PointerSegment
  | StaticSegment
  | TempSegment
  | ThisSegment
  | ThatSegment
instance Show Segment where
  show ArgumentSegment = "argument"
  show ConstantSegment = "constant"
  show LocalSegment = "local"
  show PointerSegment = "pointer"
  show StaticSegment = "static"
  show TempSegment = "temp"
  show ThisSegment = "this"
  show ThatSegment = "that"

data Target = Target Segment Int
instance Show Target where
  show (Target segment offset) =
    show segment ++ " " ++ show offset
this :: Target
this = Target PointerSegment 0
that :: Target
that = Target PointerSegment 1

data VMInstruction
  = AddInstruction
  | AndInstruction
  | NegInstruction
  | NotInstruction
  | OrInstruction
  | SubInstruction
  | EqualsInstruction
  | GreaterThanInstruction
  | LessThanInstruction
  | PopInstruction Target
  | PushInstruction Target
  | CallInstruction String Int
  | FunctionInstruction String Int
  | GotoInstruction String
  | IfGotoInstruction String
  | LabelInstruction String
  | ReturnInstruction
  | EmptyInstruction
instance Show VMInstruction where
  show AddInstruction = "add"
  show AndInstruction = "and"
  show NegInstruction = "neg"
  show NotInstruction = "not"
  show OrInstruction = "or"
  show SubInstruction = "sub"
  show EqualsInstruction = "eq"
  show GreaterThanInstruction = "gt"
  show LessThanInstruction = "lt"
  show (PopInstruction target) =
    let
      Target segment _ = target
    in
      case segment of
        ConstantSegment ->
          error "Cannot pop to constant"
        _ ->
          "pop " ++ show target
  show (PushInstruction target) = "push " ++ show target
  show (CallInstruction functionName args) =
    "call " ++ functionName ++ " " ++ show args
  show (FunctionInstruction functionName locals) =
    "function " ++ functionName ++ " " ++ show locals
  show (GotoInstruction label) = "goto " ++ label
  show (IfGotoInstruction label) = "if-goto " ++ label
  show (LabelInstruction label) = "label " ++ label
  show ReturnInstruction = "return"
  show EmptyInstruction = ""
toVMFile :: [VMInstruction] -> String
toVMFile = intercalate "\n" . map show
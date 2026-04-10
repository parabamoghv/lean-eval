import Lean
import EvalTools.Markers

open Lean

structure InventoryEntry where
  module : String
  declarationName : String
  basename : String
  deriving ToJson

def parseName (text : String) : Name :=
  text.splitOn "." |>.foldl Name.str .anonymous

def lastComponent (name : Name) : String :=
  match name with
  | .str _ s => s
  | .num p _ => lastComponent p
  | .anonymous => ""

def inventoryForModule (env : Environment) (moduleName : Name) : Array InventoryEntry :=
  match env.getModuleIdx? moduleName with
  | none => #[]
  | some moduleIdx =>
      Id.run do
        let mut entries := #[]
        for (declName, constantInfo) in env.constants do
          if env.getModuleIdxFor? declName == some moduleIdx && EvalTools.hasEvalProblemTag env declName then
            match constantInfo with
            | .thmInfo _ | .opaqueInfo _ =>
                entries := entries.push {
                  module := toString moduleName
                  declarationName := toString declName
                  basename := lastComponent declName
                }
            | _ => panic! s!"@[eval_problem] used on non-theorem declaration '{declName}'"
        entries

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let moduleNames := args.map parseName
  let env ← importModules (moduleNames.toArray.map fun moduleName => ({ module := moduleName } : Import)) {}
  let entries := moduleNames.foldl (fun acc moduleName => acc ++ inventoryForModule env moduleName) #[]
  IO.println <| Json.pretty <| toJson entries
  return 0

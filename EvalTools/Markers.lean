import Lake.Toml
import Lake.Util.Message
import Lean

open Lean
open Lean.Parser
open Lake
open Lake.Toml
open Std

set_option autoImplicit false

namespace EvalTools

structure EvalProblemMetadata where
  id : String
  title : String
  test : Bool
  moduleName : String
  theoremName : String
  author : String
  notes : Option String := none
  source : Option String := none
  informalSolution : Option String := none

def manifestRelativePath : System.FilePath :=
  "manifests" / "problems.toml"

partial def findManifestPath? (dir : System.FilePath) : IO (Option System.FilePath) := do
  let candidate := dir / manifestRelativePath
  if ← candidate.pathExists then
    return some candidate
  match dir.parent with
  | none => return none
  | some parent =>
      if parent == dir then
        return none
      findManifestPath? parent

def requireNonempty (field value : String) : EDecodeM String := do
  if value.isEmpty then
    throwDecodeErrorAt Syntax.missing s!"Manifest field `{field}` must be non-empty."
  pure value

instance : DecodeToml EvalProblemMetadata where
  decode v := do
    let t ← v.decodeTable
    let id ← requireNonempty "id" (← t.decode `id)
    let title ← requireNonempty "title" (← t.decode `title)
    let moduleName ← requireNonempty "module" (← t.decode `module)
    let theoremName ← requireNonempty "theorem" (← t.decode `theorem)
    let author ← requireNonempty "author" (← t.decode `author)
    let notes? : Option String ← t.decode? `notes
    let source? : Option String ← t.decode? `source
    let informalSolution? : Option String ← t.decode? `informal_solution
    return {
      id := id
      title := title
      test := ← t.decode `test
      moduleName := moduleName
      theoremName := theoremName
      author := author
      notes := notes?.bind fun s => if s.isEmpty then none else some s
      source := source?.bind fun s => if s.isEmpty then none else some s
      informalSolution := informalSolution?.bind fun s => if s.isEmpty then none else some s
    }

def decodeErrorsToString (errors : Array DecodeError) : String :=
  "\n".intercalate <| errors.toList.map fun err => err.msg

def parseManifestMetadata (contents : String) (fileName : String := manifestRelativePath.toString) :
    IO (Except String (Array EvalProblemMetadata)) := do
  let inputCtx := mkInputContext contents fileName
  let table ←
    match (← Lake.Toml.loadToml inputCtx |>.toBaseIO) with
    | Except.ok table => pure table
    | Except.error err => return Except.error (← Lake.mkMessageLogString err)
  let decoded :
      EStateM.Result Unit (Array DecodeError) (Array EvalProblemMetadata) :=
    (Lake.Toml.Table.decode (α := Array EvalProblemMetadata) table `problem).run #[]
  let blocks ←
    match decoded with
    | EStateM.Result.ok entries errors =>
        if errors.isEmpty then
          pure entries
        else
          return Except.error (decodeErrorsToString errors)
    | EStateM.Result.error _ errors =>
        return Except.error (decodeErrorsToString errors)
  let mut entries : Array EvalProblemMetadata := #[]
  let mut seenIds : HashSet String := {}
  let mut seenRefs : HashSet (String × String) := {}
  for metadata in blocks do
    if seenIds.contains metadata.id then
      return Except.error s!"Duplicate problem id `{metadata.id}` in `manifests/problems.toml`."
    seenIds := seenIds.insert metadata.id
    let theoremKey := (metadata.moduleName, metadata.theoremName)
    if seenRefs.contains theoremKey then
      return Except.error
        s!"Duplicate theorem reference `{metadata.moduleName}:{metadata.theoremName}` in `manifests/problems.toml`."
    seenRefs := seenRefs.insert theoremKey
    entries := entries.push metadata
  return Except.ok entries

def moduleNameForDecl (env : Environment) (declName : Name) : String :=
  match env.getModuleIdxFor? declName with
  | some idx => toString <| env.header.moduleNames[idx.toNat]!
  | none => toString env.mainModule

def theoremMatches (declName : Name) (theoremField : String) : Bool :=
  theoremField == declName.toString || theoremField == declName.getString!

def validateMatchingManifestEntry
    (declName : Name) (entries : Array EvalProblemMetadata) (moduleName : String) :
    Except String Unit := do
  let matchingEntries := entries.filter fun entry =>
    entry.moduleName == moduleName && theoremMatches declName entry.theoremName
  if matchingEntries.isEmpty then
    throw
      s!"The theorem `{declName}` is marked with @[eval_problem], but `manifests/problems.toml` has no matching `theorem = ...` entry.\nAdd a corresponding problem entry to the manifest."
  if matchingEntries.size > 1 then
    throw
      s!"The theorem `{declName}` is marked with @[eval_problem], but `manifests/problems.toml` has multiple matching entries in module `{moduleName}`."

def ensureEvalProblemManifestEntry (declName : Name) : AttrM Unit := do
  let env ← getEnv
  match env.find? declName with
  | some (.thmInfo _) | some (.opaqueInfo _) => pure ()
  | _ =>
      throwError
        "The attribute @[eval_problem] may only be applied to theorem or opaque theorem declarations, but `{declName}` is not one."
  let cwd ← IO.currentDir
  let some manifestPath ← findManifestPath? cwd
    | throwError
        "Could not find `manifests/problems.toml` while validating @[eval_problem] on `{declName}`."
  let manifestContents ← IO.FS.readFile manifestPath
  let entries ←
    match ← parseManifestMetadata manifestContents manifestPath.toString with
    | .ok entries => pure entries
    | .error err => throwError "{err}"
  let moduleName := moduleNameForDecl env declName
  match validateMatchingManifestEntry declName entries moduleName with
  | .ok () => pure ()
  | .error err => throwError "{err}"

initialize evalProblemAttr : TagAttribute ←
  registerTagAttribute `eval_problem
    "Marks theorem declarations as benchmark problems and validates their manifest metadata."
    ensureEvalProblemManifestEntry

def hasEvalProblemTag (env : Environment) (declName : Name) : Bool :=
  evalProblemAttr.hasTag env declName

end EvalTools

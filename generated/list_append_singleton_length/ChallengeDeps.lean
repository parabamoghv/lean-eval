import Mathlib

namespace FormalMathEval

/-!
The declarations in this module are the human-authored source of truth for benchmark
statements. The generator reads declarations marked with `@[eval_problem]` and emits
independent comparator workspaces from these shared source files, so benchmark authors
do not need to hand-maintain per-problem packages.
-/



/--
error: The theorem `FormalMathEval.eval_problem_manifest_guard` is marked with @[eval_problem], but `manifests/problems.toml` has no matching `theorem = ...` entry.
Add a corresponding problem entry to the manifest.
-/
#guard_msgs in
end FormalMathEval

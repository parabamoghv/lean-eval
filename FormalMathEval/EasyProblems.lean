import Mathlib
import EvalTools.Markers

namespace FormalMathEval

/-!
The declarations in this module are the human-authored source of truth for benchmark
statements. The generator reads declarations marked with `@[eval_problem]` and emits
independent comparator workspaces from these shared source files, so benchmark authors
do not need to hand-maintain per-problem packages.
-/

@[eval_problem]
theorem two_plus_two_eq_four : (2 : Nat) + 2 = 4 := by
  sorry

@[eval_problem]
theorem list_append_singleton_length :
    (([1, 2] : List Nat).append [3]).length = 3 := by
  sorry

/--
error: The theorem `FormalMathEval.eval_problem_manifest_guard` is marked with @[eval_problem], but `manifests/problems.toml` has no matching `theorem = ...` entry.
Add a corresponding problem entry to the manifest.
-/
#guard_msgs in
@[eval_problem]
theorem eval_problem_manifest_guard : (1 : Nat) = 1 := by
  rfl

def starterNumber : Nat := 4

end FormalMathEval

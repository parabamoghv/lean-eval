import Mathlib.Analysis.Real.Pi.Chudnovsky
import EvalTools.Markers

namespace FormalMathEval
namespace Analysis

open scoped Real

/-!
Chudnovsky's formula for `π⁻¹`.

Mathlib already defines the Chudnovsky series `chudnovskySum`; this benchmark asks for the missing
identity with `π⁻¹`.
-/

-- ANCHOR: chudnovsky_formula_for_pi_inv
@[eval_problem]
theorem chudnovsky_formula_for_pi_inv :
    chudnovskySum = π⁻¹ := by
  sorry
-- ANCHOR_END: chudnovsky_formula_for_pi_inv

end Analysis
end FormalMathEval

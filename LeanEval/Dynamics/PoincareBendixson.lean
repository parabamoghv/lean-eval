import Mathlib
import EvalTools.Markers

namespace LeanEval
namespace Dynamics

/-!
# Poincaré–Bendixson theorem (Poincaré 1881–1886; Bendixson 1901)

§63 of Knill's *Some Fundamental Theorems in Mathematics*. For a `C¹`
autonomous vector field `F : ℝ² → ℝ²` and a global integral curve `γ`,
the forward orbit `γ '' [0, ∞)` falls into one of three sharp branches:
it is unbounded; its ω-limit set `⋂ s, closure (γ '' [s, ∞))` contains
an equilibrium of `F`; or its ω-limit set is exactly the range of a
non-constant periodic integral curve of `F` (a genuine limit cycle).

Two refinements relative to the textbook formulation matter for
faithfulness. Case 2 is the weak form "ω-limit *contains* an equilibrium"
rather than "γ converges to an equilibrium"; this admits
heteroclinic-cycle / polycycle behaviour. (A stronger pointwise-
convergence version is falsified by the polynomial field
`F₀(x, y) = (−(x² + y² − 1)²·(y + x·(x² + y² − 1)),
            (x² + y² − 1)²·(x − y·(x² + y² − 1)))`, whose orbits spiral
toward the unit circle of equilibria without converging to any single
point.) Case 3 requires `F (β 0) ≠ 0` so that a constant equilibrium
does not vacuously satisfy the periodic branch.

Mathlib has `IsIntegralCurve` (`Mathlib/Analysis/ODE/Basic.lean`),
`omegaLimit` / `ω⁺` (`Mathlib/Dynamics/OmegaLimit.lean`), `Flow`
(`Mathlib/Dynamics/Flow.lean`), and Picard–Lindelöf local existence
(`Mathlib/Analysis/ODE/PicardLindelof.lean`). Mathlib does **not** have
the Poincaré–Bendixson theorem (`grep -ri "Poincare.*Bendix\|bendix"`
returns only Cantor–Bendixson on perfect sets, which is unrelated), the
Jordan curve theorem in `ℝ²` (a hard dependency of the classical proof
via interior/exterior separation; the same gap is the subject of §48
of Knill), the transverse-arc / first-return-map machinery, or global
continuation of `C¹` ODE flows. The Isabelle/HOL/AFP entry "Poincare-
Bendixson" by Immler–Tan exists and uses Harrison's Jordan curve
theorem — no Lean port.
-/

open Filter Topology Set

/-- Ambient space: `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Poincaré–Bendixson theorem** (sharp planar trichotomy). For a `C¹`
autonomous vector field `F : ℝ² → ℝ²` and a global integral curve `γ`,
the forward orbit `γ '' [0, ∞)` is either unbounded; or its ω-limit set
contains an equilibrium of `F`; or its ω-limit set equals the range of
a non-constant periodic integral curve of `F`. -/
@[eval_problem]
theorem poincare_bendixson
    (F : Plane → Plane) (_hF : ContDiff ℝ 1 F)
    (γ : ℝ → Plane) (_hγ : IsIntegralCurve γ (fun _ x => F x)) :
    ¬ Bornology.IsBounded (γ '' Set.Ici 0)
    ∨ (∃ x₀, F x₀ = 0 ∧ x₀ ∈ ⋂ s : ℝ, closure (γ '' Set.Ici s))
    ∨ (∃ T : ℝ, 0 < T ∧ ∃ β : ℝ → Plane,
        IsIntegralCurve β (fun _ x => F x) ∧
        (∀ t, β (t + T) = β t) ∧
        F (β 0) ≠ 0 ∧
        (⋂ s : ℝ, closure (γ '' Set.Ici s)) = Set.range β) := by
  sorry

end Dynamics
end LeanEval

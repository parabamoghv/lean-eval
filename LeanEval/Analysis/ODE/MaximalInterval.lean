import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.NNReal.Basic
import EvalTools.Markers

namespace LeanEval
namespace Analysis
namespace ODE

/-!
Maximum interval of existence and blow-up dichotomy.

Let `f : ℝ → ℝ → ℝ` be continuous and *locally* Lipschitz in the second argument: for
every `(t₀, y₀)`, there is an open neighborhood `U × W ⊆ ℝ × ℝ` and a Lipschitz constant
`L` such that `f s y` is `L`-Lipschitz in `y ∈ W`, uniformly for `s ∈ U`. (This includes
nonlinear examples such as `f t y = y²` that are *not* globally Lipschitz.)

For every initial condition `(t₀, y₀)`, the forward initial value problem
  `y'(t) = f(t, y t)`,  `y t₀ = y₀`,
admits a unique forward solution defined on a maximal interval starting at `t₀`. Either
the solution exists for all `t ≥ t₀`, or there is a finite `β > t₀` such that the
solution exists on `[t₀, β)` and *blows up* there: `|y t|` is unbounded as `t → β⁻`.

Uniqueness is included: any forward solution agrees with the maximal one on its domain.
-/

open Filter Topology
open scoped NNReal

/-- **Forward maximal interval and blow-up dichotomy.**

For continuous `f` locally Lipschitz in the second argument, the forward IVP has a unique
maximal forward solution. Either the solution is global on `[t₀, ∞)`, or blows up at some
finite `β > t₀`. Any other forward solution agrees with this maximal one on its domain. -/
@[eval_problem]
theorem maximal_interval_blowup_dichotomy
    (f : ℝ → ℝ → ℝ)
    (hf_cont : Continuous f.uncurry)
    (hf_lip : ∀ t₀ y₀ : ℝ, ∃ (U W : Set ℝ) (L : ℝ≥0),
        IsOpen U ∧ IsOpen W ∧ t₀ ∈ U ∧ y₀ ∈ W ∧
        ∀ s ∈ U, ∀ y₁ ∈ W, ∀ y₂ ∈ W,
          ‖f s y₁ - f s y₂‖ ≤ L * ‖y₁ - y₂‖)
    (t₀ y₀ : ℝ) :
    ∃ y : ℝ → ℝ,
      y t₀ = y₀ ∧
      -- Either global forward existence ...
      ((∀ t : ℝ, t₀ < t → HasDerivAt y (f t (y t)) t) ∨
       -- ... or finite-time blow-up at some β > t₀.
       ∃ β : ℝ, t₀ < β ∧
         (∀ t : ℝ, t₀ < t → t < β → HasDerivAt y (f t (y t)) t) ∧
         ∀ M : ℝ, ∃ᶠ t in nhdsWithin β (Set.Iio β), M < |y t|) ∧
      -- Uniqueness: any forward solution agrees with `y` on its domain.
      (∀ z : ℝ → ℝ, ∀ T : ℝ, t₀ < T → z t₀ = y₀ →
        (∀ t : ℝ, t₀ < t → t < T → HasDerivAt z (f t (z t)) t) →
        ∀ t : ℝ, t₀ ≤ t → t < T → z t = y t) := by
  sorry

end ODE
end Analysis
end LeanEval

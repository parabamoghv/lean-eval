import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Homeomorph.Defs
import EvalTools.Markers

namespace LeanEval
namespace Analysis
namespace ODE

/-!
Hartman–Grobman in one dimension.

For a `C¹` vector field `f : ℝ → ℝ` defined on a neighborhood of `0`, with hyperbolic
equilibrium at the origin (`f 0 = 0` and `f' 0 ≠ 0`), the flow of the nonlinear ODE
`y' = f(y)` is locally conjugate to the flow of its linearisation `y' = f'(0) · y`.

Conjugacy here is at the *flow* level, but stated in differential form: there is an open
neighborhood `U` of `0` and a homeomorphism `h` from `U` to itself (with inverse `g`),
both fixing `0`, such that for every open interval `I` and every `C¹` curve
`γ : ℝ → ℝ` whose values on `I` lie in `U`:

* if `γ` solves the linear ODE on `I`, then `h ∘ γ` solves the nonlinear ODE on `I`;
* if `γ` solves the nonlinear ODE on `I`, then `g ∘ γ` solves the linear ODE on `I`.

Asking the composed curves to satisfy the corresponding ODEs is stronger than mere
topological conjugacy: it implicitly requires `h ∘ γ` and `g ∘ γ` to be `C¹` along every
solution curve, which forces `h, g` to be differentiable on `U`. In one dimension this is
achievable: classical Hartman–Grobman in 1D admits a smooth conjugacy under just
`C¹` regularity.
-/

open Filter Topology

/-- **Hartman–Grobman, one-dimensional, local flow-conjugacy form.**

Let `f : ℝ → ℝ` be `C¹` on some open neighborhood `V` of `0`, with `f 0 = 0` and
`f' 0 ≠ 0`. Then there is a smaller open neighborhood `U` of `0` and a homeomorphism of
`U` onto itself (presented as a pair `h, g` of mutually inverse continuous self-maps of
`U`, both sending `0` to `0`) which intertwines the linear and nonlinear flows on every
open time-interval `I` along which both trajectories stay inside `U`. -/
@[eval_problem]
theorem hartman_grobman_one_dim
    (f : ℝ → ℝ) (V : Set ℝ) (hV_open : IsOpen V) (hV_zero : (0 : ℝ) ∈ V)
    (hf : ContDiffOn ℝ 1 f V) (hf0 : f 0 = 0) (hfd : deriv f 0 ≠ 0) :
    ∃ (U : Set ℝ) (h g : ℝ → ℝ),
      IsOpen U ∧ (0 : ℝ) ∈ U ∧ U ⊆ V ∧
      h 0 = 0 ∧ g 0 = 0 ∧
      Set.MapsTo h U U ∧ Set.MapsTo g U U ∧
      Set.LeftInvOn g h U ∧ Set.RightInvOn g h U ∧
      ContinuousOn h U ∧ ContinuousOn g U ∧
      (∀ I : Set ℝ, IsOpen I → ∀ γ : ℝ → ℝ,
        (∀ t ∈ I, γ t ∈ U) →
          ((∀ t ∈ I, HasDerivAt γ (deriv f 0 * γ t) t) →
            ∀ t ∈ I, HasDerivAt (h ∘ γ) (f ((h ∘ γ) t)) t) ∧
          ((∀ t ∈ I, HasDerivAt γ (f (γ t)) t) →
            ∀ t ∈ I, HasDerivAt (g ∘ γ) (deriv f 0 * (g ∘ γ) t) t)) := by
  sorry

end ODE
end Analysis
end LeanEval

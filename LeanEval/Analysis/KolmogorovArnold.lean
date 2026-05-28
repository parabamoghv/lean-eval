import Mathlib
import EvalTools.Markers

namespace LeanEval
namespace Analysis

/-!
# Kolmogorov–Arnold superposition theorem (Kolmogorov 1957 / Arnold 1957 / Lorentz 1962)

§80 of Knill's *Some Fundamental Theorems in Mathematics*. Every
continuous function of `n` variables on the unit cube `[0, 1]ⁿ` is a
finite superposition of continuous functions of *one* variable and
addition. In the Lorentz form there exist continuous inner functions
`φ_{k,l} : ℝ → ℝ` and a single continuous outer function `g : ℝ → ℝ`
with

  `f(x₁, …, xₙ) = ∑_{k=0}^{2n} g(∑_{l=1}^{n} φ_{k,l}(x_l))`.

Since `h(x, y) = x + y` is a two-variable continuous function, this
exhibits `f` as built from one- and two-variable continuous functions,
resolving the *continuous* form of Hilbert's 13th problem.

We encode the representation on the unit cube `Set.Icc (0 : Fin n → ℝ) 1`
with the inner and outer functions continuous on all of `ℝ` (a Tietze
extension makes this equivalent to continuity on `[0, 1]`). We follow
Knill in letting both `g` and the `φ_{k,l}` depend on `f` — the
existence form, slightly weaker than Kolmogorov's universal-inner-
functions refinement, but exactly Knill's statement.

Mathlib has `ContinuousOn` and finite `Finset.sum` — enough to state the
representation with no new definitions — but no Kolmogorov–Arnold
superposition theorem. The only `Kolmogorov` hits in mathlib are the
probabilistic extension and zero-one theorems (unrelated). No
dedicated external Lean project, no in-flight mathlib PR.
-/

open scoped BigOperators

/-- **Kolmogorov–Arnold superposition theorem.** For `n ≥ 1`, every
continuous `f` on the unit cube `[0,1]ⁿ` admits a representation
`f(x) = ∑_{k=0}^{2n} g(∑_{l=1}^{n} φ_{k,l}(x_l))` with a single
continuous outer function `g : ℝ → ℝ` and continuous inner functions
`φ_{k,l} : ℝ → ℝ` (Lorentz 1962 form). -/
@[eval_problem]
theorem kolmogorov_arnold (n : ℕ) (_hn : 1 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (_hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ (g : ℝ → ℝ) (φ : Fin (2 * n + 1) → Fin n → ℝ → ℝ),
      Continuous g ∧ (∀ k l, Continuous (φ k l)) ∧
      ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
        f x = ∑ k, g (∑ l, φ k l (x l)) := by
  sorry

end Analysis
end LeanEval

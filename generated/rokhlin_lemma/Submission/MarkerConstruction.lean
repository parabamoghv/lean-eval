import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.RokhlinCore
import Submission.BasinCoverage
import Submission.CondExpInvariant
import Submission.BasinCondExp
import Submission.CondNonAtomic
import Submission.KernelNonAtomic

/-!
# Marker construction for basin coverage

Proves `exists_small_condExp_pos_marker`: for any δ > 0, there exists A with
μ(A) ≤ δ and condExp(1_A | I_T) > 0 a.e., which immediately gives
`exists_small_set_large_basin` via `basin_full_of_condExp_pos`.
-/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Submission.RokhlinCore Submission.BasinCoverage Submission.CondExpInvariant
open Submission.BasinCondExp Submission.CondNonAtomic Submission.KernelNonAtomic
open Classical

noncomputable section

namespace Submission.MarkerConstruction

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-! ### Pulling out I_T-measurable factors from condExp -/

/-
For I_T-measurable S and any measurable A:
condExp(1_{A ∩ S} | I_T) = 1_S · condExp(1_A | I_T) a.e.
-/
theorem condExp_indicator_inter_invariant
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {A : Set Ω} (hA : MeasurableSet A)
    {S : Set Ω} (hS : @MeasurableSet Ω (invSigmaAlgebra T) S) :
    (μ[(A ∩ S).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T])
      =ᵐ[μ]
    fun x => S.indicator (fun x => (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) x := by
  refine' MeasureTheory.condExp_congr_ae _ |> fun h => h.trans _;
  exact Set.indicator S ( fun x => ( Set.indicator A fun x => 1 ) x );
  · filter_upwards [ ] with x using by by_cases hx : x ∈ S <;> by_cases hx' : x ∈ A <;> simp +decide [ hx, hx' ] ;
  · convert MeasureTheory.condExp_indicator _ _ using 1;
    · exact MeasureTheory.integrable_indicator_iff hA |>.2 ( MeasureTheory.integrable_const _ );
    · grind

/-
condExp is monotone: A ⊆ B → condExp(1_A) ≤ condExp(1_B) a.e.
-/
theorem condExp_indicator_mono
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {A B : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    ∀ᵐ x ∂μ, (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x ≤
              (μ[B.indicator (fun _ => (1 : ℝ)) | m]) x := by
  convert MeasureTheory.condExp_mono _ _ _ using 1;
  all_goals try infer_instance;
  · rw [ MeasureTheory.integrable_indicator_iff ] <;> aesop;
  · exact MeasureTheory.integrable_indicator_iff ( by aesop ) |>.2 ( MeasureTheory.integrable_const _ );
  · filter_upwards [ ] with x using Set.indicator_le_indicator_of_subset hAB ( fun _ => zero_le_one ) x

/-! ### Main construction -/

/-
For any δ > 0, there exists A with μ(A) ≤ δ and condExp(1_A|I_T) > 0 a.e.
This is proved by constructing a marker from the countable separating family
using the halving trick combined with condExp_not_zero_one_ae.
-/
theorem exists_small_condExp_pos_marker
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {δ : ENNReal} (hδ : 0 < δ) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A ≤ δ ∧
      (∀ᵐ x ∂μ, 0 < (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
  have := @Submission.KernelNonAtomic.exists_small_condExp_pos_marker;
  exact this μ T hT hap hδ

end Submission.MarkerConstruction

end
import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.RokhlinCore
import Submission.BasinCoverage
import Submission.ErgodicDecomp
import Submission.BasinCondExp
import Submission.CondNonAtomic
import Submission.CondExpInvariant
import Submission.MarkerConstruction

/-!
# General basin coverage — bridge infrastructure

Provides `exists_small_set_large_basin_v2`, an equivalent of
`exists_small_set_large_basin` that handles both cases:
1. Positive-infimum case — delegates to `exists_small_set_large_basin_of_pos_infimum`.
2. Zero-infimum case — uses generator atoms + basin coverage.
-/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Submission.RokhlinCore Submission.BasinCoverage Submission.ErgodicDecomp
open Submission.BasinCondExp Submission.CondNonAtomic Submission.CondExpInvariant
open Submission.MarkerConstruction
open Classical

noncomputable section

namespace Submission.GeneralBasin

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Orbits stay in invariant sets -/

theorem ae_orbit_stays_in_invariant (μ : Measure Ω) [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {R : Set Ω} (hR : MeasurableSet R) (hRinv : R =ᵐ[μ] T ⁻¹' R) :
    ∀ᵐ x ∂μ, x ∈ R → ∀ k : ℕ, T^[k] x ∈ R := by
  rw [ MeasureTheory.ae_iff ] at *;
  rw [ Filter.EventuallyEq ] at hRinv;
  rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ];
  simp_all +decide [ Set.preimage ];
  filter_upwards [ hRinv, MeasureTheory.ae_all_iff.2 fun n => hT.iterate n |>.quasiMeasurePreserving.ae ( hRinv ) ] with x hx₁ hx₂ hx₃ n;
  exact Nat.recOn n hx₃ fun n ih => by simpa only [ Function.iterate_succ_apply' ] using hx₂ n |>.1 ih;

theorem basin_ae_subset_invariant (μ : Measure Ω) [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {R : Set Ω} (hR : MeasurableSet R) (hRinv : R =ᵐ[μ] T ⁻¹' R)
    {A : Set Ω} (hAR : A ⊆ R) :
    ∀ᵐ x ∂μ, x ∈ Rᶜ → x ∉ basin T A := by
  have h_complement_subset : ∀ᵐ x ∂μ, x ∈ Rᶜ → ∀ k, T^[k] x ∈ Rᶜ := by
    have := @ae_orbit_stays_in_invariant;
    specialize this μ hT ( hR.compl ) ; simp_all +decide [ Set.compl_def ] ;
    exact this ( by rw [ Filter.eventuallyEq_set ] at *; filter_upwards [ hRinv ] with x hx; aesop );
  filter_upwards [ h_complement_subset ] with x hx hx' hx'';
  obtain ⟨ k, hk ⟩ := hx'';
  grind

theorem measure_basin_compl_split (μ : Measure Ω) [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {R : Set Ω} (hR : MeasurableSet R) (hRinv : R =ᵐ[μ] T ⁻¹' R)
    {A : Set Ω} (hA : MeasurableSet A) (hAR : A ⊆ R) :
    μ (basin T A)ᶜ ≤ μ (R \ basin T A) + μ Rᶜ := by
  refine' le_trans _ ( MeasureTheory.measure_union_le _ _ );
  refine' MeasureTheory.measure_mono_ae _;
  filter_upwards [ basin_ae_subset_invariant μ hT hR hRinv hAR ] with x hx using by tauto;

/-! ### Main theorem -/

theorem exists_small_set_large_basin_v2
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {δ : ENNReal} (hδ : 0 < δ) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A ≤ δ ∧ μ (basin T A)ᶜ ≤ δ := by
  by_cases h : ∃ α : ENNReal, 0 < α ∧
    ∀ E : Set Ω, MeasurableSet E → E =ᵐ[μ] T ⁻¹' E → 0 < μ E → α ≤ μ E
  · -- Case 1: positive infimum globally
    obtain ⟨α, hα, hαb⟩ := h
    exact exists_small_set_large_basin_of_pos_infimum μ T hT hap hδ α hα hαb
  · -- Case 2: zero infimum — use marker with positive conditional expectation
    push_neg at h
    obtain ⟨A, hA_meas, hA_small, hA_condExp⟩ :=
      exists_small_condExp_pos_marker μ T hT hap hδ
    exact ⟨A, hA_meas, hA_small,
      le_of_eq (basin_full_of_condExp_pos μ hT hA_meas hA_condExp) |>.trans (zero_le δ)⟩

end Submission.GeneralBasin

end

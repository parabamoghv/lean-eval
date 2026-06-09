import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.RokhlinCore
import Submission.BasinCoverage
import Submission.CondExpInvariant

/-!
# Basin coverage via conditional expectation

This file establishes key links between the basin complement and conditional
expectation given the invariant σ-algebra.

## Main results

* `eventualAvoid` — the exactly-invariant a.e. representative of `(basin T A)ᶜ`
* `eventualAvoid_strictly_invariant` — `T⁻¹(eventualAvoid) = eventualAvoid`
* `eventualAvoid_ae_eq_basin_compl` — `eventualAvoid =ᵐ (basin T A)ᶜ`
* `condExp_eq_zero_on_basin_compl` — `condExp I_T 1_A = 0` a.e. on `(basin T A)ᶜ`
* `basin_full_of_condExp_pos` — `condExp I_T 1_A > 0` a.e. ⟹ `μ((basin T A)ᶜ) = 0`
-/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Submission.RokhlinCore Submission.BasinCoverage Submission.CondExpInvariant
open Classical

noncomputable section

namespace Submission.BasinCondExp

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-! ### The eventual avoidance set -/

/-- `eventualAvoid T A` = {x | ∃ k, ∀ j ≥ k, T^[j] x ∉ A}

This is the set of points whose forward orbit eventually permanently avoids A.
It is exactly T-invariant and a.e. equal to `(basin T A)ᶜ`. -/
def eventualAvoid (T : Ω → Ω) (A : Set Ω) : Set Ω :=
  {x | ∃ k : ℕ, ∀ j : ℕ, k ≤ j → T^[j] x ∉ A}

/-- `(basin T A)ᶜ ⊆ eventualAvoid T A` -/
theorem basin_compl_subset_eventualAvoid {T : Ω → Ω} {A : Set Ω} :
    (basin T A)ᶜ ⊆ eventualAvoid T A := by
  intro x hx
  refine ⟨0, fun j _ => ?_⟩
  exact fun h => hx (mem_iUnion.mpr ⟨j, h⟩)

/-
`T⁻¹(eventualAvoid T A) = eventualAvoid T A`
-/
theorem preimage_eventualAvoid_eq {T : Ω → Ω} {A : Set Ω} :
    T ⁻¹' eventualAvoid T A = eventualAvoid T A := by
  ext x;
  constructor <;> rintro ⟨ k, hk ⟩;
  · exact ⟨ k + 1, fun j hj => by simpa only [ ← Function.iterate_succ_apply' ] using hk ( j - 1 ) ( Nat.le_sub_one_of_lt hj ) |> fun h => by cases j <;> tauto ⟩;
  · exact ⟨ k, fun j hj => by simpa only [ ← Function.iterate_succ_apply' ] using hk ( j + 1 ) ( by linarith ) ⟩

/-
`eventualAvoid T A` is measurable
-/
theorem measurableSet_eventualAvoid {T : Ω → Ω} (hT : Measurable T)
    {A : Set Ω} (hA : MeasurableSet A) :
    MeasurableSet (eventualAvoid T A) := by
  rw [ show eventualAvoid T A = ⋃ k : ℕ, ⋂ j ∈ Set.Ici k, ( T^[j] ) ⁻¹' Aᶜ from ?_ ];
  · exact MeasurableSet.iUnion fun k => MeasurableSet.biInter ( Set.to_countable _ ) fun j hj => MeasurableSet.preimage ( hA.compl ) ( hT.iterate j );
  · ext x; simp [eventualAvoid]

/-- `eventualAvoid T A` is in the invariant σ-algebra -/
theorem eventualAvoid_invSigmaAlgebra {T : Ω → Ω} (hT : Measurable T)
    {A : Set Ω} (hA : MeasurableSet A) :
    @MeasurableSet Ω (invSigmaAlgebra T) (eventualAvoid T A) := by
  rw [measurableSet_invSigmaAlgebra_iff]
  exact ⟨measurableSet_eventualAvoid hT hA, preimage_eventualAvoid_eq⟩

/-
`μ(eventualAvoid T A) = μ((basin T A)ᶜ)`
-/
theorem measure_eventualAvoid_eq (μ : Measure Ω) [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {A : Set Ω} (hA : MeasurableSet A) :
    μ (eventualAvoid T A) = μ (basin T A)ᶜ := by
  have h_eventualAvoid_eq : ∀ k : ℕ, μ (⋂ j ∈ Set.Ici k, T^[j] ⁻¹' Aᶜ) = μ (basin T A)ᶜ := by
    intro k;
    convert hT.iterate k |>.measure_preimage _ using 2;
    · simp +decide [ Set.ext_iff, basin ];
      exact fun x => ⟨ fun hx i => by simpa only [ ← Function.iterate_add_apply, add_comm ] using hx ( i + k ) ( by linarith ), fun hx i hi => by simpa only [ ← Function.iterate_add_apply, add_comm ] using hx ( i - k ) |> fun h => by simpa only [ ← Function.iterate_add_apply, Nat.sub_add_cancel hi ] using h ⟩;
    · refine' MeasurableSet.nullMeasurableSet _;
      exact MeasurableSet.compl ( basin_measurableSet ( hT.measurable ) hA );
  rw [ show eventualAvoid T A = ⋃ k : ℕ, ⋂ j ∈ Set.Ici k, T^[j] ⁻¹' Aᶜ from ?_ ];
  · refine' le_antisymm _ _;
    · refine' le_of_tendsto_of_tendsto' ( MeasureTheory.tendsto_measure_iUnion_atTop _ ) tendsto_const_nhds fun n => _;
      · exact fun k l hkl => Set.biInter_subset_biInter_left fun j hj => Nat.le_trans hkl hj;
      · exact h_eventualAvoid_eq n ▸ le_rfl;
    · refine' le_trans _ ( MeasureTheory.measure_mono <| Set.subset_iUnion _ 0 );
      exact h_eventualAvoid_eq 0 ▸ le_rfl;
  · ext x; simp [eventualAvoid]

/-
`eventualAvoid T A =ᵐ[μ] (basin T A)ᶜ`
-/
theorem eventualAvoid_ae_eq_basin_compl (μ : Measure Ω) [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    eventualAvoid T A =ᵐ[μ] (basin T A)ᶜ := by
  have h_eq : μ (eventualAvoid T A) = μ (basin T A)ᶜ :=
    measure_eventualAvoid_eq μ hT hA
  have h_sub : (basin T A)ᶜ ⊆ eventualAvoid T A := basin_compl_subset_eventualAvoid
  have h_nm : NullMeasurableSet (basin T A)ᶜ μ :=
    (basin_measurableSet hT.measurable hA).compl.nullMeasurableSet
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · -- μ(eventualAvoid \ basin_compl) = 0
    rw [MeasureTheory.measure_diff]
    · rw [h_eq]
      exact tsub_self (μ (basin T A)ᶜ)
    · exact h_sub
    · exact h_nm
    · exact ne_top_of_le_ne_top (measure_ne_top μ _) (measure_mono h_sub)
  · -- μ(basin_compl \ eventualAvoid) = 0
    rw [Set.diff_eq_empty.mpr]
    · rw [measure_empty]
    · exact h_sub


/-
`μ(eventualAvoid T A ∩ A) = 0`
-/
theorem measure_eventualAvoid_inter_marker (μ : Measure Ω) [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    μ (eventualAvoid T A ∩ A) = 0 := by
  rw [ ← MeasureTheory.measure_congr ];
  any_goals exact ( basin T A ) ᶜ ∩ A;
  · rw [ show ( basin T A ) ᶜ ∩ A = ∅ by rw [ Set.inter_comm, inter_basin_compl_eq_empty ] ] ; norm_num;
  · exact MeasureTheory.ae_eq_set_inter ( eventualAvoid_ae_eq_basin_compl μ hT hA |> fun h => h.symm ) ( MeasureTheory.ae_eq_refl _ )

/-! ### Conditional expectation bridge -/

/-
If N is I_T-measurable with T⁻¹(N) = N and μ(A ∩ N) = 0, then μ(basin T A ∩ N) = 0
-/
theorem measure_basin_inter_invariant_disjoint (μ : Measure Ω) [IsFiniteMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A)
    {N : Set Ω} (hN_inv : T ⁻¹' N = N) (hN_meas : MeasurableSet N)
    (hAN : μ (A ∩ N) = 0) :
    μ (basin T A ∩ N) = 0 := by
  have h_zero : ∀ k : ℕ, μ ((T^[k])⁻¹' A ∩ N) = 0 := by
    intro k
    have h_zero : μ ((T^[k])⁻¹' (A ∩ N)) = 0 := by
      convert hAN using 1;
      exact hT.iterate k |>.measure_preimage ( by measurability );
    -- Since $T^{-1}(N) = N$, we have $T^{-k}(N) = N$ for any $k$.
    have h_inv_k : (T^[k])⁻¹' N = N := by
      exact Nat.recOn k ( by simp ) fun n ihn => by simp_all +decide [Set.ext_iff] ;
    convert h_zero using 2 ; aesop;
  rw [ basin ];
  rw [ Set.iUnion_inter, MeasureTheory.measure_iUnion_null_iff ] ; aesop

/-
`condExp I_T 1_A = 0` a.e. on `(basin T A)ᶜ`
-/
theorem condExp_eq_zero_on_basin_compl (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ, x ∈ (basin T A)ᶜ →
      (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x = 0 := by
  have h_condExp_zero : ∫ x in eventualAvoid T A, (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x ∂μ = 0 := by
    rw [ setIntegral_condExp ( invSigmaAlgebra_le T ) ];
    · convert MeasureTheory.integral_eq_zero_of_ae ( show ∀ᵐ x ∂μ.restrict ( eventualAvoid T A ), ( Set.indicator A ( fun _ => 1 : Ω → ℝ ) ) x = 0 from ?_ ) using 1;
      rw [ MeasureTheory.ae_restrict_iff' ];
      · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( measure_eventualAvoid_inter_marker μ hT hA ) ] with x hx hx' using by aesop;
      · apply_rules [ measurableSet_eventualAvoid ];
        exact hT.measurable;
    · exact MeasureTheory.integrable_indicator_iff hA |>.2 ( MeasureTheory.integrable_const _ );
    · convert @Submission.BasinCondExp.eventualAvoid_invSigmaAlgebra Ω m₀ T hT.measurable A hA using 1;
  rw [ MeasureTheory.integral_eq_zero_iff_of_nonneg_ae ] at h_condExp_zero;
  · have h_eq : eventualAvoid T A =ᵐ[μ] (basin T A)ᶜ := by
      apply_rules [ eventualAvoid_ae_eq_basin_compl ];
    rw [ Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' ] at h_condExp_zero;
    · filter_upwards [ h_condExp_zero, h_eq ] with x hx₁ hx₂ hx₃ using hx₁ ( by simpa using hx₂.mpr hx₃ );
    · exact measurableSet_eventualAvoid ( hT.measurable ) hA;
  · have h_condExp_nonneg : 0 ≤ᵐ[μ] μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T] := by
      apply_rules [ MeasureTheory.condExp_nonneg ];
      exact Filter.Eventually.of_forall fun x => by by_cases hx : x ∈ A <;> simp +decide [ hx ] ;
    exact MeasureTheory.ae_restrict_of_ae h_condExp_nonneg;
  · refine' MeasureTheory.Integrable.integrableOn _;
    fun_prop

/-
If `condExp I_T 1_A > 0` a.e., then basin T A covers Ω a.e.
-/
theorem basin_full_of_condExp_pos (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A)
    (hpos : ∀ᵐ x ∂μ, 0 < (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) :
    μ (basin T A)ᶜ = 0 := by
  rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ];
  filter_upwards [ hpos, condExp_eq_zero_on_basin_compl μ hT hA ] with x hx₁ hx₂ using fun hx₃ => hx₁.ne' ( hx₂ hx₃ )

end Submission.BasinCondExp

end

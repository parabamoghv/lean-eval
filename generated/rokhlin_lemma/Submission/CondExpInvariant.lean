import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.BasinCoverage

/-!
# Conditional Expectation and Invariant σ-algebra Infrastructure

This file provides reusable infrastructure for the zero-infimum case of
`exists_small_set_large_basin`.
-/

open MeasureTheory Set Function
open Submission.RokhlinCore Submission.BasinCoverage Submission.Helpers
open Classical

noncomputable section

namespace Submission.CondExpInvariant

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-! ### Basin complement basic properties -/

/-- A ∩ (basin T A)ᶜ = ∅. -/
theorem inter_basin_compl_eq_empty {T : Ω → Ω} {A : Set Ω} :
    A ∩ (basin T A)ᶜ = ∅ := by
  ext x
  constructor
  · rintro ⟨hxA, hxnot⟩; exact absurd (basin_superset hxA) hxnot
  · simp

/-- basin T A = A ∪ T⁻¹(basin T A). -/
theorem basin_eq_union_preimage' {T : Ω → Ω} {A : Set Ω} :
    basin T A = A ∪ T ⁻¹' basin T A := by
  ext x; simp only [basin, mem_iUnion, mem_preimage, mem_union]
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact Or.inl hk
    | succ n => exact Or.inr ⟨n, by rwa [iterate_succ_apply] at hk⟩
  · rintro (hx | ⟨k, hk⟩)
    · exact ⟨0, hx⟩
    · exact ⟨k + 1, by rwa [iterate_succ_apply]⟩

/-- T⁻¹(basin T A) ⊆ basin T A. -/
theorem preimage_basin_subset' {T : Ω → Ω} {A : Set Ω} :
    T ⁻¹' basin T A ⊆ basin T A := by
  intro x hx
  simp only [basin, mem_iUnion, mem_preimage] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  exact ⟨k + 1, by rwa [iterate_succ_apply]⟩

/-! ### Generating family basin coverage -/

/-- For any set G, basin T G ∪ basin T Gᶜ = univ. -/
theorem basin_union_basin_compl (T : Ω → Ω) (G : Set Ω) :
    basin T G ∪ basin T Gᶜ = univ := by
  ext x; simp only [mem_union, mem_univ, iff_true]
  by_cases hx : x ∈ basin T G
  · exact Or.inl hx
  · right
    simp only [basin, mem_iUnion, mem_preimage] at hx ⊢
    push_neg at hx
    exact ⟨0, hx 0⟩

/-! ### Invariant σ-algebra -/

/-- The invariant σ-algebra for T: sets S with T⁻¹(S) = S. -/
def invSigmaAlgebra (T : Ω → Ω) : MeasurableSpace Ω where
  MeasurableSet' s := @MeasurableSet Ω m₀ s ∧ T ⁻¹' s = s
  measurableSet_empty := ⟨@MeasurableSet.empty Ω m₀, preimage_empty⟩
  measurableSet_compl s hs := ⟨@MeasurableSet.compl Ω s m₀ hs.1,
    by rw [preimage_compl, hs.2]⟩
  measurableSet_iUnion f hf := ⟨@MeasurableSet.iUnion Ω ℕ m₀ _ f (fun i => (hf i).1),
    by rw [preimage_iUnion]; exact iUnion_congr (fun i => (hf i).2)⟩

/-- The invariant σ-algebra is a sub-σ-algebra. -/
theorem invSigmaAlgebra_le (T : Ω → Ω) :
    invSigmaAlgebra T ≤ m₀ := by
  intro s ⟨hs, _⟩; exact hs

/-- Characterization of measurability in the invariant σ-algebra. -/
theorem measurableSet_invSigmaAlgebra_iff {T : Ω → Ω} {s : Set Ω} :
    @MeasurableSet Ω (invSigmaAlgebra T) s ↔ @MeasurableSet Ω m₀ s ∧ T ⁻¹' s = s :=
  Iff.rfl

/-- The trimmed measure is sigma-finite when μ is finite. -/
instance sigmaFinite_trim_invSigmaAlgebra (T : Ω → Ω) (μ : Measure Ω)
    [IsFiniteMeasure μ] :
    SigmaFinite (μ.trim (invSigmaAlgebra_le T)) := by
  haveI : IsFiniteMeasure (μ.trim (invSigmaAlgebra_le T)) := by
    constructor
    rw [trim_measurableSet_eq (invSigmaAlgebra_le T)
        ⟨MeasurableSet.univ, by simp [preimage_univ]⟩]
    exact measure_lt_top μ _
  infer_instance

/-! ### Non-returning set has measure zero -/

/-
The non-returning set has measure zero (Poincaré recurrence).
-/
theorem measure_nonReturning_eq_zero (μ : Measure Ω) {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A)
    [IsFiniteMeasure μ] :
    μ (A \ T ⁻¹' basin T A) = 0 := by
  rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ];
  have h_recurrence : ∀ᵐ x ∂μ, x ∈ A → ∃ᶠ k in Filter.atTop, T^[k] x ∈ A := by
    apply_rules [ Submission.MarkerLemmas.ae_frequently_return ];
    grind +suggestions;
  filter_upwards [ h_recurrence ] with x hx hx' ; simp_all +decide [ basin ] ;
  exact hx ( Filter.eventually_atTop.mpr ⟨ 1, fun k hk => hx'.2 ( k - 1 ) |> fun h => by cases k <;> tauto ⟩ )

/-
The basin complement is a.e. strictly invariant.
-/
theorem basin_compl_ae_eq_preimage' (μ : Measure Ω) {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A)
    [IsFiniteMeasure μ] :
    T ⁻¹' (basin T A)ᶜ =ᵐ[μ] (basin T A)ᶜ := by
  -- Apply the lemma measure_preimage_basin_compl_diff_eq_zero to conclude the proof.
  have := measure_preimage_basin_compl_diff_eq_zero μ hT hA;
  exact (by
  rw [ MeasureTheory.ae_eq_set ];
  refine' ⟨ this, _ ⟩;
  exact MeasureTheory.measure_mono_null ( fun x hx => by have := basin_compl_forward_invariant hx.1; aesop ) ( MeasureTheory.measure_empty ))

/-! ### condExp of indicator vanishes on strictly invariant disjoint sets -/

/-
The integral of condExp I_T (1_A) over a strictly invariant
    set C disjoint from A equals 0.
-/
theorem condExp_indicator_zero_on_invariant_disjoint
    (μ : Measure Ω) {T : Ω → Ω}
    {A C : Set Ω} (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hC_inv : T ⁻¹' C = C) (hAC : Disjoint A C)
    [IsFiniteMeasure μ] :
    ∫ x in C, (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x ∂μ = 0 := by
  rw [ MeasureTheory.setIntegral_condExp ];
  · rw [ MeasureTheory.integral_eq_zero_of_ae ];
    filter_upwards [ MeasureTheory.ae_restrict_mem hC ] with x hx using Set.indicator_of_notMem ( fun h => hAC.le_bot ⟨ h, hx ⟩ ) _;
  · exact MeasureTheory.integrable_indicator_iff hA |>.2 ( MeasureTheory.integrable_const _ );
  · exact ⟨ hC, hC_inv ⟩

/-! ### ⋂_k T^{-k}((basin T A)ᶜ) = (basin T A)ᶜ -/

/-
⋂_k T^{-k}((basin T A)ᶜ) = (basin T A)ᶜ.
-/
theorem iInter_preimage_basin_compl_eq {T : Ω → Ω} {A : Set Ω} :
    ⋂ k : ℕ, (T^[k]) ⁻¹' (basin T A)ᶜ = (basin T A)ᶜ := by
  refine' Set.Subset.antisymm _ _;
  · exact Set.iInter_subset_of_subset 0 ( by simp +decide );
  · intro x hx;
    simp_all +decide [ basin ];
    exact fun i j => by simpa only [ ← Function.iterate_add_apply ] using hx ( j + i ) ;

end Submission.CondExpInvariant

end
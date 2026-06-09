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
# Conditional non-atomicity of the invariant σ-algebra
-/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Submission.RokhlinCore Submission.BasinCoverage Submission.CondExpInvariant
open Classical

noncomputable section

namespace Submission.CondNonAtomic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-- The "degenerate" set: where every generator has 0-1 conditional expectation. -/
def fullDegSet (T : Ω → Ω) (μ : Measure Ω) (G : ℕ → Set Ω) : Set Ω :=
  ⋂ n, ({x | (μ[Set.indicator (G n) (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x = 0} ∪
         {x | (μ[Set.indicator (G n) (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x = 1})

/-! ### Helper lemmas for the conditional expectation argument -/

/-
E[1_{T⁻¹A}|I_T] =ᵃᵉ E[1_A|I_T] when T is measure-preserving.

Proof sketch: For any I_T-measurable S (so T⁻¹S = S):
  ∫_S 1_{T⁻¹A} dμ = μ(S ∩ T⁻¹A) = μ(T⁻¹(S ∩ A)) = μ(S ∩ A) = ∫_S 1_A dμ
Use ae_eq_condExp_of_forall_setIntegral_eq or condExp uniqueness.
-/
theorem condExp_preimage_indicator_ae_eq
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {A : Set Ω} (hA : @MeasurableSet Ω m₀ A) :
    (μ[Set.indicator (T ⁻¹' A) (fun _ => (1 : ℝ)) | invSigmaAlgebra T])
      =ᵐ[μ]
    (μ[Set.indicator A (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) := by
  apply_rules [ ae_eq_condExp_of_forall_setIntegral_eq ];
  · exact MeasureTheory.integrable_indicator_iff hA |>.2 ( MeasureTheory.integrable_const _ );
  · intro s hs hμs; exact MeasureTheory.Integrable.integrableOn ( by exact MeasureTheory.integrable_condExp ) ;
  · intro s hs hμs
    have h_eq : ∫ x in s, (Set.indicator A (fun _ => (1 : ℝ))) x ∂μ = ∫ x in s, (Set.indicator (T ⁻¹' A) (fun _ => (1 : ℝ))) x ∂μ := by
      have h_eq : μ (s ∩ A) = μ (s ∩ T ⁻¹' A) := by
        have h_inv : MeasurableSet s ∧ T ⁻¹' s = s := by
          rw [ measurableSet_invSigmaAlgebra_iff ] at hs ; tauto;
        have h_eq : μ (s ∩ A) = μ (T ⁻¹' (s ∩ A)) := by
          rw [ hT.measure_preimage ] ; aesop;
        aesop;
      convert congr_arg ENNReal.toReal h_eq using 1 <;> rw [ MeasureTheory.integral_indicator ] <;> norm_num [ hs, hA ];
      · rw [ Set.inter_comm, MeasureTheory.measureReal_def ];
      · rw [ MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply ];
        · rw [ Set.inter_comm ];
        · exact hT.measurable hA;
      · exact hT.measurable hA;
    rw [ h_eq, setIntegral_condExp ];
    · exact MeasureTheory.integrable_indicator_iff ( hT.measurable hA ) |>.2 ( MeasureTheory.integrable_const _ );
    · grind;
  · exact MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable

/-
On {E[1_A|m] = 1}, we have A a.e. Equivalently, μ({E[1_A|m] = 1} \ A) = 0.

Proof sketch: Let S = {E[1_A|m] = 1}, which is m-measurable (since condExp is
StronglyMeasurable w.r.t. m by stronglyMeasurable_condExp). By setIntegral_condExp:
  ∫_S E[1_A|m] dμ = ∫_S 1_A dμ = μ(S ∩ A).
But ∫_S E[1_A|m] dμ = ∫_S 1 dμ = μ(S) since E[1_A|m] = 1 on S.
So μ(S ∩ A) = μ(S), hence μ(S \ A) = 0.
-/
theorem measure_condExp_one_sdiff
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {A : Set Ω} (hA : @MeasurableSet Ω m₀ A) :
    μ ({x | (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x = 1} \ A) = 0 := by
  by_contra h_contra;
  obtain ⟨S, hS_meas, hS⟩ : ∃ S : Set Ω, MeasurableSet S ∧ μ (S \ A) ≠ 0 ∧ ∀ᵐ x ∂μ, x ∈ S → (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x = 1 := by
    obtain ⟨S, hS_meas, hS⟩ : ∃ S : Set Ω, MeasurableSet S ∧ μ (S \ A) ≠ 0 ∧ ∀ᵐ x ∂μ, x ∈ S → (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x = 1 := by
      have h_meas : MeasurableSet {x | (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x = 1} := by
        exact measurableSet_eq_fun ( by exact stronglyMeasurable_condExp.measurable ) measurable_const
      exact ⟨ _, h_meas, h_contra, Filter.Eventually.of_forall fun x hx => hx ⟩;
    use S;
  have h_int_eq : ∫ x in S, (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x ∂μ = ∫ x in S, (A.indicator (fun _ => (1 : ℝ))) x ∂μ := by
    apply_rules [ MeasureTheory.setIntegral_condExp ];
    exact MeasureTheory.integrable_indicator_iff hA |>.2 ( MeasureTheory.integrable_const _ );
  have h_int_eq : ∫ x in S, (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x ∂μ = μ.real S := by
    rw [ MeasureTheory.integral_congr_ae ];
    any_goals exact fun x => 1;
    · simp +decide [ MeasureTheory.measureReal_def ];
    · rw [ Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' ] <;> aesop;
  have h_int_eq : ∫ x in S, (A.indicator (fun _ => (1 : ℝ))) x ∂μ = μ.real (S ∩ A) := by
    rw [ MeasureTheory.integral_indicator ] <;> norm_num [ hA, hS_meas ];
    rw [ Set.inter_comm ];
  have h_int_eq : μ.real S = μ.real (S ∩ A) + μ.real (S \ A) := by
    simp +decide [ MeasureTheory.measureReal_def ];
    rw [ ← ENNReal.toReal_add, ← MeasureTheory.measure_inter_add_diff S hA ]; all_goals exact MeasureTheory.measure_ne_top _ _;
  simp_all +decide [ MeasureTheory.measureReal_def ];
  exact hS.1 ( by rw [ ENNReal.toReal_eq_zero_iff ] at h_int_eq; aesop )

/-
On {E[1_A|m] = 0}, A is null. Equivalently, μ({E[1_A|m] = 0} ∩ A) = 0.

Proof sketch: Let S = {E[1_A|m] = 0}, which is m-measurable. By setIntegral_condExp:
  ∫_S E[1_A|m] dμ = ∫_S 1_A dμ = μ(S ∩ A).
But ∫_S E[1_A|m] dμ = 0 since E[1_A|m] = 0 on S. So μ(S ∩ A) = 0.
-/
theorem measure_condExp_zero_inter
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    {A : Set Ω} (hA : @MeasurableSet Ω m₀ A) :
    μ ({x | (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x = 0} ∩ A) = 0 := by
  by_contra h_contra;
  have h_integral_zero : ∫ x in {x | (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x = 0}, (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x ∂μ = 0 := by
    rw [ MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero ] ; aesop;
  have h_integral_indicator : ∫ x in {x | (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x = 0}, (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x ∂μ = ∫ x in {x | (μ[A.indicator (fun _ => (1 : ℝ)) | m]) x = 0} ∩ A, (1 : ℝ) ∂μ := by
    convert setIntegral_condExp hm _ _ using 1;
    · exact?;
    · infer_instance;
    · exact MeasureTheory.integrable_indicator_iff hA |>.2 ( MeasureTheory.integrable_const _ );
    · exact measurableSet_eq_fun ( by exact MeasureTheory.StronglyMeasurable.measurable ( MeasureTheory.stronglyMeasurable_condExp ) ) measurable_const;
  simp_all +decide [ MeasureTheory.measureReal_def ];
  exact h_contra ( by rw [ ENNReal.toReal_eq_zero_iff ] at h_integral_zero; aesop )

/-! ### Main theorem -/

/-
On fullDegSet, x ∈ G_n ↔ T(x) ∈ G_n a.e.

Uses the three helper lemmas:
- condExp_preimage_indicator_ae_eq: E[1_{T⁻¹G_n}|I_T] =ᵃᵉ E[1_{G_n}|I_T]
- measure_condExp_one_sdiff: {E=1} ⊆ A a.e.
- measure_condExp_zero_inter: A ∩ {E=0} is null

On fullDegSet, E[1_{G_n}|I_T] ∈ {0,1}. So:
  x ∈ G_n ↔ E(x) = 1  (by the two measure-zero helpers)
  x ∈ T⁻¹(G_n) ↔ E'(x) = 1  (same helpers for T⁻¹G_n)
  E = E'  a.e. (by condExp_preimage_indicator_ae_eq)
Hence G_n ∩ fullDegSet =ᵃᵉ T⁻¹(G_n) ∩ fullDegSet.
-/
theorem generator_invariant_on_fullDegSet
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    (n : ℕ) :
    ∀ᵐ x ∂μ, x ∈ fullDegSet T μ G →
      (x ∈ G n ↔ T x ∈ G n) := by
  obtain ⟨g, hg⟩ : ∃ g : Ω → ℝ, (μ[Set.indicator (G n) (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) =ᵐ[μ] g ∧ (μ[Set.indicator (T ⁻¹' (G n)) (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) =ᵐ[μ] g := by
    exact ⟨ _, Filter.EventuallyEq.rfl, condExp_preimage_indicator_ae_eq μ hT ( hG n ) ⟩;
  have hN1 : μ ({x | g x = 1} \ G n) = 0 := by
    have hN1 : μ ({x | (μ[Set.indicator (G n) (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x = 1} \ G n) = 0 := by
      convert measure_condExp_one_sdiff μ ( invSigmaAlgebra_le T ) ( hG n ) using 1;
    rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ] at *;
    filter_upwards [ hN1, hg.1 ] with x hx₁ hx₂ using by aesop;
  have hN2 : μ ({x | g x = 0} ∩ G n) = 0 := by
    have hN2 : μ ({x | (μ[Set.indicator (G n) (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x = 0} ∩ G n) = 0 := by
      apply_rules [ measure_condExp_zero_inter ];
    rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ] at *;
    filter_upwards [ hg.1, hN2 ] with x hx₁ hx₂ using by aesop;
  have hN3 : μ ({x | g x = 1} \ T ⁻¹' (G n)) = 0 := by
    have hN3 : μ ({x | (μ[Set.indicator (T ⁻¹' (G n)) (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x = 1} \ T ⁻¹' (G n)) = 0 := by
      convert measure_condExp_one_sdiff μ ( invSigmaAlgebra_le T ) ( hT.measurable ( hG n ) ) using 1;
    refine' MeasureTheory.measure_mono_null _ ( MeasureTheory.measure_union_null hN3 ( MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hg.2.symm ) );
    intro x hx; by_cases h : g x = μ[(T ⁻¹' G n).indicator fun x => 1 | invSigmaAlgebra T] x <;> aesop;
  have hN4 : μ ({x | g x = 0} ∩ T ⁻¹' (G n)) = 0 := by
    have hN4 : μ ({x | (μ[Set.indicator (T ⁻¹' (G n)) (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x = 0} ∩ T ⁻¹' (G n)) = 0 := by
      apply_rules [ measure_condExp_zero_inter ];
      exact hT.measurable ( hG n );
    rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ] at *;
    filter_upwards [ hg.2, hN4 ] with x hx₁ hx₂ using by aesop;
  filter_upwards [ hg.1, hg.2, MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hN1, MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hN2, MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hN3, MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hN4 ] with x hx1 hx2 hx3 hx4 hx5 hx6;
  simp_all +decide [ fullDegSet ];
  grind

/-- On fullDegSet, T = id a.e. -/
theorem ae_id_on_fullDegSet
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    {G : ℕ → Set Ω} (hG_meas : ∀ n, MeasurableSet (G n))
    (hG_sep : ∀ x y : Ω, x ≠ y →
      ∃ n, (x ∈ G n ∧ y ∉ G n) ∨ (x ∉ G n ∧ y ∈ G n)) :
    ∀ᵐ x ∂μ, x ∈ fullDegSet T μ G → T x = x := by
  have h_all : ∀ᵐ x ∂μ, ∀ n, x ∈ fullDegSet T μ G → (x ∈ G n ↔ T x ∈ G n) :=
    ae_all_iff.mpr fun n => generator_invariant_on_fullDegSet μ hT hG_meas n
  filter_upwards [h_all] with x hx hxF
  by_contra h_ne
  obtain ⟨n, hn⟩ := hG_sep x (T x) (fun h => h_ne (h.symm))
  cases hn with
  | inl h => exact h.2 ((hx n hxF).mp h.1)
  | inr h => exact h.1 ((hx n hxF).mpr h.2)

/-- μ(fullDegSet) = 0 for aperiodic T. -/
theorem condExp_not_zero_one_ae
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {G : ℕ → Set Ω} (hG_meas : ∀ n, MeasurableSet (G n))
    (hG_sep : ∀ x y : Ω, x ≠ y →
      ∃ n, (x ∈ G n ∧ y ∉ G n) ∨ (x ∉ G n ∧ y ∈ G n)) :
    μ (fullDegSet T μ G) = 0 := by
  have h_id := ae_id_on_fullDegSet μ T hT hG_meas hG_sep
  refine le_antisymm ?_ (zero_le _)
  calc μ (fullDegSet T μ G)
      ≤ μ (periodicPts T) := by
        refine measure_mono_ae ?_
        filter_upwards [h_id] with x hid hxF
        exact ⟨1, Nat.one_pos, by simp [IsPeriodicPt, IsFixedPt, hid hxF]⟩
    _ = 0 := hap

end Submission.CondNonAtomic

end
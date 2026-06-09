import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.RokhlinCore
import Submission.BasinCoverage
import Submission.CondExpInvariant
import Submission.CondNonAtomic

/-!
# Kernel T-invariance and non-atomicity

We prove that the conditional kernel κ_ω = condExpKernel μ (invSigmaAlgebra T)
is T-invariant and non-atomic for a.e. ω.
-/

open LeanEval.Dynamics
open MeasureTheory Set Function ProbabilityTheory
open Submission.RokhlinCore Submission.BasinCoverage Submission.CondExpInvariant
open Submission.CondNonAtomic
open Classical

noncomputable section

namespace Submission.KernelInvariance

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Ω : Type*} [m₀ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-! ### Connection between kernel and conditional expectation -/

theorem kernel_real_eq_condExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) {S : Set Ω} (hS : MeasurableSet S) :
    (fun ω => ((condExpKernel μ (invSigmaAlgebra T)) ω S).toReal) =ᵐ[μ]
    (μ[S.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) := by
  have h := @condExpKernel_ae_eq_condExp' Ω (invSigmaAlgebra T) m₀ _ μ _ S hS
  rwa [inf_eq_left.mpr (invSigmaAlgebra_le T)] at h

theorem kernel_preimage_eq_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) {S : Set Ω} (hS : MeasurableSet S) :
    ∀ᵐ ω ∂μ, (condExpKernel μ (invSigmaAlgebra T)) ω (T ⁻¹' S) =
              (condExpKernel μ (invSigmaAlgebra T)) ω S := by
  have := @ Submission.KernelInvariance.kernel_real_eq_condExp;
  have := @this Ω m₀ ‹_› μ ‹_› T ( T ⁻¹' S ) ?_;
  · rename_i h;
    filter_upwards [ this, h μ T hS, condExp_preimage_indicator_ae_eq μ hT hS ] with ω hω₁ hω₂ hω₃;
    rw [ ← ENNReal.toReal_eq_toReal_iff' ];
    · rw [ hω₁, hω₂, hω₃ ];
    · exact MeasureTheory.measure_ne_top _ _;
    · exact MeasureTheory.measure_ne_top _ _;
  · exact hT.measurable hS

/-! ### Universal T-invariance via π-λ -/

/-
For a.e. ω, (κ_ω).map T = κ_ω.
-/
theorem kernel_T_invariant_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    ∀ᵐ ω ∂μ, (condExpKernel μ (invSigmaAlgebra T) ω).map T =
              condExpKernel μ (invSigmaAlgebra T) ω := by
  by_contra h;
  -- Since m₀ is countably generated, we can find a countable collection of sets {G_n} that generate m₀.
  obtain ⟨G, hG_countable, hG_gen⟩ : ∃ G : ℕ → Set Ω, Set.Countable (Set.range G) ∧ m₀ = MeasurableSpace.generateFrom (Set.range G) := by
    rcases MeasurableSpace.CountablyGenerated.isCountablyGenerated ( α := Ω ) with ⟨ G, hG_countable, hG_gen ⟩;
    have := hG_countable.exists_eq_range;
    rcases G.eq_empty_or_nonempty with ( rfl | hG_nonempty ) <;> simp_all +decide;
    · exact ⟨ fun _ => ∅, Set.countable_range _, by simp +decide ⟩;
    · exact ⟨ this.choose, Set.countable_range _, this.choose_spec ▸ rfl ⟩;
  -- Consider the finite intersection closure S of the range of G.
  set S := {s : Set Ω | ∃ F : Finset ℕ, s = ⋂ i ∈ F, G i} with hS_def
  have hS_pi_system : IsPiSystem S := by
    intro s hs t ht hst; obtain ⟨ F, rfl ⟩ := hs; obtain ⟨ G, rfl ⟩ := ht; simp +decide [ Set.iInter_inter ] ;
    use F ∪ G; simp +decide [ Finset.mem_union, Set.iInter_inter_distrib ] ;
    ext; simp +decide [ Set.mem_iInter, Set.mem_inter_iff ] ; aesop;
  have hS_gen : MeasurableSpace.generateFrom S = m₀ := by
    refine' le_antisymm _ _;
    · refine' MeasurableSpace.generateFrom_le _;
      rintro s ⟨ F, rfl ⟩;
      exact MeasurableSet.biInter ( Finset.countable_toSet F ) fun i hi => hG_gen.symm ▸ MeasurableSpace.measurableSet_generateFrom ( Set.mem_range_self i );
    · rw [ hG_gen ];
      exact MeasurableSpace.generateFrom_mono ( Set.range_subset_iff.mpr fun n => ⟨ { n }, by simp +decide ⟩ );
  -- For a.e. ω, for all s ∈ S, κ_ω(T⁻¹ s) = κ_ω(s).
  have h_ae_agree_S : ∀ᵐ ω ∂μ, ∀ s ∈ S, (condExpKernel μ (invSigmaAlgebra T)) ω (T ⁻¹' s) = (condExpKernel μ (invSigmaAlgebra T)) ω s := by
    have h_ae_agree_S : ∀ s ∈ S, ∀ᵐ ω ∂μ, (condExpKernel μ (invSigmaAlgebra T)) ω (T ⁻¹' s) = (condExpKernel μ (invSigmaAlgebra T)) ω s := by
      intro s hs
      obtain ⟨F, hF⟩ := hs
      have h_meas : MeasurableSet s := by
        exact hF.symm ▸ MeasurableSet.biInter ( Finset.countable_toSet F ) fun i _ => hG_gen.symm ▸ MeasurableSpace.measurableSet_generateFrom ( Set.mem_range_self i );
      convert kernel_preimage_eq_ae μ T hT h_meas using 1;
    have h_countable_S : Set.Countable S := by
      exact Set.countable_range ( fun F : Finset ℕ => ⋂ i ∈ F, G i ) |> Set.Countable.mono fun s hs => by aesop;
    rw [ MeasureTheory.ae_ball_iff h_countable_S ] ; aesop;
  refine' h ( h_ae_agree_S.mono fun ω hω => _ );
  apply MeasureTheory.Measure.ext_of_generateFrom_of_cover;
  exact hS_gen.symm;
  any_goals exact Set.countable_singleton Set.univ;
  · exact hS_pi_system;
  · simp +decide;
  · simp +decide [ Measure.map_apply_of_aemeasurable, hT.aemeasurable ];
  · simp +zetaDelta at *;
    intro a; specialize hω a; rw [ Measure.map_apply_of_aemeasurable ] ; aesop;
    · exact hT.measurable.aemeasurable;
    · exact MeasurableSet.biInter ( Finset.countable_toSet a ) fun i hi => hG_gen.symm ▸ MeasurableSpace.measurableSet_generateFrom ( Set.mem_range_self i );
  · simp +decide [ Measure.map_apply_of_aemeasurable, hT.measurable.aemeasurable ]

/-! ### Atoms of T-invariant probability measures are periodic -/

/-
If ν is a T-invariant probability measure and ν({y}) > 0, then y ∈ periodicPts T.
-/
theorem atom_of_invariant_is_periodic
    (T : Ω → Ω) {ν : Measure Ω} [IsProbabilityMeasure ν]
    (hν : ν.map T = ν) (hTm : Measurable T) {y : Ω} (hy : ν {y} > 0) :
    y ∈ periodicPts T := by
  -- Since ν is T-invariant, we have ν(T^k {y}) ≥ ν({y}) for all k.
  have h_bound : ∀ k : ℕ, ν (T^[k] ⁻¹' {y}) ≥ ν {y} := by
    intro k
    have h_bound_k : ν (T^[k] ⁻¹' {y}) ≥ ν {y} := by
      have h_bound_k_step : ∀ z, ν (T ⁻¹' {T z}) ≥ ν {z} := by
        exact fun z => MeasureTheory.measure_mono ( Set.singleton_subset_iff.mpr ( Set.mem_preimage.mpr rfl ) )
      induction' k with k ih generalizing y <;> simp_all +decide [ Function.iterate_succ_apply', Set.preimage_comp ];
      rw [ ← MeasureTheory.Measure.map_apply hTm ] ; aesop;
      exact hTm.iterate k ( MeasurableSingletonClass.measurableSet_singleton _ )
    generalize_proofs at *; (
    exact h_bound_k)
  generalize_proofs at *;
  -- By contradiction, assume y is not periodic.
  by_contra h_not_periodic;
  -- Since y is not periodic, the sets T^k {y} are pairwise disjoint.
  have h_disjoint : ∀ k m : ℕ, k ≠ m → Disjoint (T^[k] ⁻¹' {y}) (T^[m] ⁻¹' {y}) := by
    intro k m hkm; rw [ Set.disjoint_left ] ; intro x hxk hxm; simp_all +decide [ periodicPts ] ;
    cases' lt_or_gt_of_ne hkm with hkm hkm <;> simp_all +decide [ IsPeriodicPt, IsFixedPt ];
    · have h_contradiction : T^[m-k] y = y := by
        rw [ ← hxk, ← Function.iterate_add_apply, Nat.sub_add_cancel hkm.le, hxm ];
        exact hxk.symm
      generalize_proofs at *; exact h_not_periodic (m - k) (Nat.sub_pos_of_lt hkm) h_contradiction;
    · have h_contradiction : T^[k-m] y = y := by
        rw [ ← hxm, ← Function.iterate_add_apply, Nat.sub_add_cancel hkm.le, hxk ];
        exact hxm.symm
      generalize_proofs at *;
      exact h_not_periodic ( k - m ) ( Nat.sub_pos_of_lt hkm ) h_contradiction
  generalize_proofs at *;
  -- Since the sets T^k {y} are pairwise disjoint and each has measure at least ν {y}, their union has infinite measure.
  have h_union_infinite : ν (⋃ k : ℕ, T^[k] ⁻¹' {y}) = ⊤ := by
    rw [ MeasureTheory.measure_iUnion ];
    · exact le_top.antisymm ( le_trans ( by simp +decide [ hy.ne' ] ) ( ENNReal.tsum_le_tsum h_bound ) );
    · exact fun k m hkm => h_disjoint k m hkm;
    · exact fun k => MeasurableSet.preimage ( MeasurableSingletonClass.measurableSet_singleton _ ) ( hTm.iterate k )
  generalize_proofs at *;
  exact h_union_infinite.not_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide ) )

/-! ### Kernel periodic mass is zero a.e. -/

/-
κ_ω(periodicPts T) = 0 a.e.
-/
theorem kernel_periodicPts_zero_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ) :
    ∀ᵐ ω ∂μ, (condExpKernel μ (invSigmaAlgebra T)) ω (periodicPts T) = 0 := by
  have h_eq : ∀ᵐ ω ∂μ, ((condExpKernel μ (invSigmaAlgebra T)) ω (periodicPts T)).toReal = ((μ[(Set.indicator (periodicPts T) (fun _ => (1 : ℝ))) | invSigmaAlgebra T]) ω) := by
    apply_rules [ kernel_real_eq_condExp ];
    convert Submission.MeasurabilityLemmas.measurableSet_periodicPts T hT.measurable;
  have h_zero : ∀ᵐ ω ∂μ, ((μ[(Set.indicator (periodicPts T) (fun _ => (1 : ℝ))) | invSigmaAlgebra T]) ω) = 0 := by
    -- Since periodicPts T is measurable and has measure zero, its indicator function is zero almost everywhere.
    have h_indicator_zero : (Set.indicator (periodicPts T) (fun _ => (1 : ℝ))) =ᵐ[μ] 0 := by
      filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hap ] with x hx using by aesop;
    convert MeasureTheory.condExp_congr_ae h_indicator_zero using 1;
    rw [ MeasureTheory.condExp_zero ];
    rfl;
  filter_upwards [ h_eq, h_zero ] with ω hω₁ hω₂;
  rw [ ← ENNReal.toReal_eq_toReal_iff' ] <;> aesop

/-! ### Kernel is non-atomic a.e. -/

/-- For a.e. ω, κ_ω has no atoms. -/
theorem kernel_nonatomic_ae (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ) :
    ∀ᵐ ω ∂μ, ∀ y : Ω, (condExpKernel μ (invSigmaAlgebra T)) ω {y} = 0 := by
  filter_upwards [kernel_T_invariant_ae μ T hT,
                   kernel_periodicPts_zero_ae μ T hT hap] with ω hω_inv hω_per y
  by_contra hy
  push_neg at hy
  have hy_pos : (condExpKernel μ (invSigmaAlgebra T)) ω {y} > 0 := pos_iff_ne_zero.mpr hy
  have hy_per : y ∈ periodicPts T :=
    atom_of_invariant_is_periodic T hω_inv hT.measurable hy_pos
  have h_le : (condExpKernel μ (invSigmaAlgebra T)) ω {y} ≤
              (condExpKernel μ (invSigmaAlgebra T)) ω (periodicPts T) :=
    measure_mono (singleton_subset_iff.mpr hy_per)
  rw [hω_per] at h_le
  exact absurd h_le (not_le.mpr hy_pos)

end Submission.KernelInvariance

end
import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.RokhlinCore
import Submission.BasinCoverage
import Submission.ErgodicDecomp

/-! ## Invariant σ-algebra and restricted ergodic covering

This file provides:
1. The restricted ergodic covering lemma: an ergodic covering of an invariant
   subset (rather than all of Ω).
2. Basin coverage from a restricted covering with a small "junk" invariant set.
3. The step-down lemma: if α > 0 on Cᶜ and μ(C) ≤ δ, then
   exists_small_set_large_basin holds.
-/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Submission.RokhlinCore Submission.BasinCoverage Submission.ErgodicDecomp
open Classical

noncomputable section

namespace Submission.InvariantSigmaAlgebra

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Restricted ergodic covering -/

set_option maxHeartbeats 800000 in
/-- When every positive-measure invariant subset of C₀ has measure ≥ α > 0,
    a finite disjoint family of ergodic pieces covers C₀ a.e.
    This is the restricted version of `exists_ergodic_covering_of_pos_infimum`. -/
theorem exists_ergodic_covering_restricted
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {C₀ : Set Ω} (hC₀_meas : MeasurableSet C₀)
    (hC₀_inv : C₀ =ᵐ[μ] T ⁻¹' C₀)
    (hC₀_pos : 0 < μ C₀)
    (α : ENNReal) (hα : 0 < α)
    (hα_bound : ∀ E : Set Ω, MeasurableSet E → E ⊆ C₀ → E =ᵐ[μ] T ⁻¹' E →
      0 < μ E → α ≤ μ E) :
    ∃ E : ℕ → Set Ω,
      (∀ k, MeasurableSet (E k)) ∧
      (∀ k, E k ⊆ C₀) ∧
      (∀ k, 0 < μ (E k) → IsErgodicOn μ T (E k)) ∧
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      μ (C₀ \ ⋃ k, E k) = 0 := by
  -- Let's choose any finite family of ergodic pieces from C₀ with maximum cardinality.
  obtain ⟨E, hE⟩ : ∃ E : Finset (Set Ω), (∀ i ∈ E, MeasurableSet i ∧ i ⊆ C₀ ∧ i =ᵐ[μ] T ⁻¹' i ∧ 0 < μ i ∧ IsErgodicOn μ T i) ∧ (∀ i ∈ E, ∀ j ∈ E, i ≠ j → Disjoint i j) ∧ (∀ F : Finset (Set Ω), (∀ i ∈ F, MeasurableSet i ∧ i ⊆ C₀ ∧ i =ᵐ[μ] T ⁻¹' i ∧ 0 < μ i ∧ IsErgodicOn μ T i) → (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint i j) → F.card ≤ E.card) := by
    have h_finite : Set.Finite {k : ℕ | ∃ E : Finset (Set Ω), (∀ i ∈ E, MeasurableSet i ∧ i ⊆ C₀ ∧ i =ᵐ[μ] T ⁻¹' i ∧ 0 < μ i ∧ IsErgodicOn μ T i) ∧ (∀ i ∈ E, ∀ j ∈ E, i ≠ j → Disjoint i j) ∧ E.card = k} := by
      refine' Set.finite_iff_bddAbove.mpr ⟨ ⌊ ( μ C₀ / α ).toReal⌋₊, fun k hk => _ ⟩;
      obtain ⟨ E, hE₁, hE₂, rfl ⟩ := hk;
      have h_card_le : ∑ i ∈ E, μ i ≤ μ C₀ := by
        rw [ ← MeasureTheory.measure_biUnion_finset ];
        · exact MeasureTheory.measure_mono ( Set.iUnion₂_subset fun i hi => hE₁ i hi |>.2.1 );
        · exact fun i hi j hj hij => hE₂ i hi j hj hij;
        · exact fun i hi => hE₁ i hi |>.1;
      have h_card_le : E.card * α ≤ μ C₀ := by
        refine' le_trans _ h_card_le;
        exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun i hi => hα_bound i ( hE₁ i hi |>.1 ) ( hE₁ i hi |>.2.1 ) ( hE₁ i hi |>.2.2.1 ) ( hE₁ i hi |>.2.2.2.1 ) );
      refine' Nat.le_floor _;
      rw [ ← ENNReal.toReal_le_toReal ] at * <;> norm_num at *;
      · rwa [ le_div_iff₀ ( ENNReal.toReal_pos hα.ne' ( by aesop ) ) ];
      · exact ne_of_lt ( lt_of_le_of_lt h_card_le ( MeasureTheory.measure_lt_top _ _ ) );
    obtain ⟨k, hk⟩ : ∃ k ∈ {k : ℕ | ∃ E : Finset (Set Ω), (∀ i ∈ E, MeasurableSet i ∧ i ⊆ C₀ ∧ i =ᵐ[μ] T ⁻¹' i ∧ 0 < μ i ∧ IsErgodicOn μ T i) ∧ (∀ i ∈ E, ∀ j ∈ E, i ≠ j → Disjoint i j) ∧ E.card = k}, ∀ j ∈ {k : ℕ | ∃ E : Finset (Set Ω), (∀ i ∈ E, MeasurableSet i ∧ i ⊆ C₀ ∧ i =ᵐ[μ] T ⁻¹' i ∧ 0 < μ i ∧ IsErgodicOn μ T i) ∧ (∀ i ∈ E, ∀ j ∈ E, i ≠ j → Disjoint i j) ∧ E.card = k}, k ≥ j := by
      apply_rules [ Set.exists_max_image ];
      exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
    rcases hk.1 with ⟨ E, hE₁, hE₂, rfl ⟩ ; exact ⟨ E, hE₁, hE₂, fun F hF₁ hF₂ => hk.2 _ ⟨ F, hF₁, hF₂, rfl ⟩ ⟩ ;
  -- If the remainder C₀ \ ⋃E has positive measure, it's invariant (intersection of C₀ and complement of union of invariant sets), so by `exists_ergodicOn_subset_of_pos_infimum` we can find another ergodic piece - contradicting maximality.
  by_cases h_remainder : 0 < μ (C₀ \ ⋃ i ∈ E, i);
  · obtain ⟨F, hF_meas, hF_subset, hF_inv, hF_pos, hF_erg⟩ : ∃ F : Set Ω, MeasurableSet F ∧ F ⊆ C₀ \ ⋃ i ∈ E, i ∧ F =ᶠ[ae μ] T ⁻¹' F ∧ 0 < μ F ∧ IsErgodicOn μ T F := by
      apply exists_ergodicOn_subset_of_pos_infimum;
      exact hT;
      exact hC₀_meas.diff ( MeasurableSet.biUnion ( Finset.countable_toSet E ) fun i hi => hE.1 i hi |>.1 );
      exact h_remainder;
      any_goals exact hα;
      · simp +decide [ Set.preimage_diff, Set.preimage_iUnion ];
        refine' MeasureTheory.ae_eq_set_diff hC₀_inv _;
        have h_union_inv : ∀ i ∈ E, i =ᵐ[μ] T ⁻¹' i := by
          exact fun i hi => hE.1 i hi |>.2.2.1;
        simp +zetaDelta at *;
        exact Finset.eventuallyEq_iUnion E h_union_inv;
      · exact fun E hE₁ hE₂ hE₃ hE₄ => hα_bound E hE₁ ( fun x hx => hE₂ hx |>.1 ) hE₃ hE₄;
    have := hE.2.2 ( Insert.insert F E ) ?_ ?_ <;> simp +decide at *;
    · contrapose! this;
      rw [ Finset.card_insert_of_notMem ] ; simp +decide [ hF_subset ];
      exact fun h => hF_pos.ne' ( MeasureTheory.measure_mono_null ( fun x hx => by have := hF_subset hx; aesop ) ( MeasureTheory.measure_empty ) );
    · exact ⟨ ⟨ hF_meas, fun x hx => hF_subset hx |>.1, hF_inv, hF_pos, hF_erg ⟩, fun i hi => hE.1 i hi ⟩;
    · exact ⟨ fun i hi hi' => Set.disjoint_left.mpr fun x hx hx' => by have := hF_subset hx; aesop, fun i hi => ⟨ fun hi' => Set.disjoint_left.mpr fun x hx hx' => by have := hF_subset hx'; aesop, fun j hj hij => hE.2.1 i hi j hj hij ⟩ ⟩;
  · -- Let's define the sequence E' such that E' k is the k-th element of E if k is within the cardinality of E, and empty otherwise.
    obtain ⟨E', hE'⟩ : ∃ E' : ℕ → Set Ω, (∀ k, MeasurableSet (E' k)) ∧ (∀ k, E' k ⊆ C₀) ∧ (∀ k, 0 < μ (E' k) → IsErgodicOn μ T (E' k)) ∧ (∀ i j, i ≠ j → Disjoint (E' i) (E' j)) ∧ ⋃ k, E' k = ⋃ i ∈ E, i := by
      obtain ⟨E', hE'⟩ : ∃ E' : Fin E.card → Set Ω, (∀ k, MeasurableSet (E' k)) ∧ (∀ k, E' k ⊆ C₀) ∧ (∀ k, 0 < μ (E' k) → IsErgodicOn μ T (E' k)) ∧ (∀ i j, i ≠ j → Disjoint (E' i) (E' j)) ∧ ⋃ k, E' k = ⋃ i ∈ E, i := by
        have hE'_exists : Nonempty (Fin E.card ≃ E) := by
          exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
        obtain ⟨ e ⟩ := hE'_exists;
        refine' ⟨ fun k => e k, _, _, _, _, _ ⟩ <;> simp +decide [ hE ];
        · exact fun i j hij => hE.2.1 _ ( e i |>.2 ) _ ( e j |>.2 ) ( by simpa [ Fin.ext_iff ] using fun h => hij <| e.injective <| Subtype.ext h );
        · ext x; simp [e.surjective.exists];
          exact ⟨ fun ⟨ i, hi ⟩ => ⟨ _, e i |>.2, hi ⟩, fun ⟨ i, hi, hi' ⟩ => ⟨ e.symm ⟨ i, hi ⟩, by simpa using hi' ⟩ ⟩;
      refine' ⟨ fun k => if hk : k < E.card then E' ⟨ k, hk ⟩ else ∅, _, _, _, _, _ ⟩ <;> simp +decide [ hE' ];
      · intro k; split_ifs <;> simp +decide [ * ] ;
      · intro k; split_ifs <;> [ exact hE'.2.1 _; exact Set.empty_subset _ ] ;
      · intro k hk; split_ifs at hk ⊢ <;> simp_all +decide ;
      · intro i j hij; split_ifs <;> simp +decide [ *, Set.disjoint_left ] ;
      · convert hE'.2.2.2.2 using 1;
        ext x; simp [Set.mem_iUnion];
        exact ⟨ fun ⟨ i, hi ⟩ => by split_ifs at hi <;> [ exact ⟨ _, hi ⟩ ; exact False.elim ( absurd hi ( by simp +decide ) ) ], fun ⟨ i, hi ⟩ => ⟨ i, by simpa using hi ⟩ ⟩;
    exact ⟨ E', hE'.1, hE'.2.1, hE'.2.2.1, hE'.2.2.2.1, by simpa [ hE'.2.2.2.2 ] using le_antisymm ( le_of_not_gt h_remainder ) ( zero_le _ ) ⟩

/-! ### Basin coverage from restricted covering -/

/-
If an invariant set C has μ(C) ≤ δ, and the complement Cᶜ is covered a.e. by
    a countable disjoint family of ergodic sets, then exists_small_set_large_basin holds.
-/
theorem exists_small_set_large_basin_from_complement_covering
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {δ : ENNReal} (hδ : 0 < δ)
    {C : Set Ω} (hC_meas : MeasurableSet C) (hC_inv : C =ᵐ[μ] T ⁻¹' C)
    (hC_small : μ C ≤ δ)
    (E : ℕ → Set Ω)
    (hE_meas : ∀ k, MeasurableSet (E k))
    (hE_sub : ∀ k, E k ⊆ Cᶜ)
    (hE_erg : ∀ k, 0 < μ (E k) → IsErgodicOn μ T (E k))
    (hE_disj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hE_cover : μ (Cᶜ \ ⋃ k, E k) = 0) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A ≤ δ ∧ μ (basin T A)ᶜ ≤ δ := by
  -- Place markers in each ergodic piece, exactly as in exists_small_set_large_basin_of_covering
  have hna : NoAtoms μ := Submission.NoAtoms.noAtoms_of_aperiodic μ T hT hap
  have h_marker : ∀ k, ∃ Ak : Set Ω, MeasurableSet Ak ∧ Ak ⊆ E k ∧
      μ Ak ≤ δ * μ (E k) ∧ μ (E k \ basin T Ak) = 0 := by
    intro k
    by_cases hk : 0 < μ (E k)
    · obtain ⟨Ak, hm, hsub, hpos, hle⟩ := exists_small_measurableSet_subset μ (hE_meas k) hk
        (ENNReal.mul_pos hδ.ne' hk.ne')
      exact ⟨Ak, hm, hsub, hle, (hE_erg k hk).basin_full hT hk hm hsub hpos⟩
    · push_neg at hk; have hk0 := le_antisymm hk (zero_le _)
      exact ⟨∅, MeasurableSet.empty, empty_subset _, by simp [hk0],
        le_antisymm (le_trans (measure_mono diff_subset) (le_of_eq hk0)) (zero_le _)⟩
  choose Ak hAk_meas hAk_sub hAk_le hAk_basin using h_marker
  refine ⟨⋃ k, Ak k, MeasurableSet.iUnion hAk_meas, ?_, ?_⟩
  · -- μ(⋃ Ak) ≤ δ
    have h_sum_E : ∑' k, μ (E k) ≤ 1 := by
      rw [← measure_iUnion hE_disj hE_meas]
      exact le_trans (measure_mono (subset_univ _)) (le_of_eq measure_univ)
    calc μ (⋃ k, Ak k)
        ≤ ∑' k, μ (Ak k) := measure_iUnion_le _
      _ ≤ ∑' k, δ * μ (E k) := ENNReal.tsum_le_tsum hAk_le
      _ = δ * ∑' k, μ (E k) := ENNReal.tsum_mul_left
      _ ≤ δ * 1 := by gcongr
      _ = δ := mul_one _
  · -- μ((basin T A)ᶜ) ≤ δ
    -- basin covers each E_k a.e., hence Cᶜ a.e.
    apply le_trans _ hC_small
    -- (basin T A)ᶜ ⊆ᵐ C, so μ((basin T A)ᶜ) ≤ μ(C)
    -- First show basin covers Cᶜ a.e.
    have h_covers_Cc : μ (Cᶜ \ basin T (⋃ k, Ak k)) = 0 := by
      rw [basin_iUnion]
      apply le_antisymm _ (zero_le _)
      calc μ (Cᶜ \ ⋃ k, basin T (Ak k))
          ≤ μ ((Cᶜ \ ⋃ k, E k) ∪ ⋃ k, (E k \ basin T (Ak k))) := by
            apply measure_mono; intro x hx
            simp only [mem_diff, mem_iUnion, mem_union] at *
            by_cases hxE : ∃ k, x ∈ E k
            · obtain ⟨k, hk⟩ := hxE
              right; exact ⟨k, hk, fun h' => hx.2 ⟨k, h'⟩⟩
            · left; exact ⟨hx.1, hxE⟩
        _ ≤ μ (Cᶜ \ ⋃ k, E k) + μ (⋃ k, (E k \ basin T (Ak k))) :=
            measure_union_le _ _
        _ = 0 + μ (⋃ k, (E k \ basin T (Ak k))) := by rw [hE_cover]
        _ ≤ 0 + ∑' k, μ (E k \ basin T (Ak k)) :=
            add_le_add_right (measure_iUnion_le _) _
        _ = 0 := by simp [hAk_basin]
    -- Now: (basin T A)ᶜ ⊆ C ∪ (Cᶜ \ basin T A), and the latter has measure 0
    calc μ (basin T (⋃ k, Ak k))ᶜ
        ≤ μ (C ∪ (Cᶜ \ basin T (⋃ k, Ak k))) := by
          apply measure_mono; intro x hx
          by_cases hxC : x ∈ C
          · exact Or.inl hxC
          · exact Or.inr ⟨hxC, hx⟩
      _ ≤ μ C + μ (Cᶜ \ basin T (⋃ k, Ak k)) := measure_union_le _ _
      _ = μ C + 0 := by rw [h_covers_Cc]
      _ = μ C := add_zero _

/-! ### Step-down: positive infimum on complement -/

/-
If there exists an invariant set C with μ(C) ≤ δ, and the infimum of
    positive-measure invariant subsets of Cᶜ is positive, then
    exists_small_set_large_basin holds.
-/
theorem exists_small_set_large_basin_from_pos_infimum_complement
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {δ : ENNReal} (hδ : 0 < δ)
    {C : Set Ω} (hC_meas : MeasurableSet C) (hC_inv : C =ᵐ[μ] T ⁻¹' C)
    (hC_small : μ C ≤ δ)
    (α : ENNReal) (hα : 0 < α)
    (hα_bound : ∀ E : Set Ω, MeasurableSet E → E ⊆ Cᶜ → E =ᵐ[μ] T ⁻¹' E →
      0 < μ E → α ≤ μ E) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A ≤ δ ∧ μ (basin T A)ᶜ ≤ δ := by
  -- Get covering of Cᶜ
  by_cases hCc_pos : 0 < μ Cᶜ
  · obtain ⟨E, hE_meas, hE_sub, hE_erg, hE_disj, hE_cover⟩ :=
      exists_ergodic_covering_restricted μ T hT hap hC_meas.compl
        hC_inv.compl hCc_pos α hα hα_bound
    exact exists_small_set_large_basin_from_complement_covering μ T hT hap hδ
      hC_meas hC_inv hC_small E hE_meas hE_sub hE_erg hE_disj hE_cover
  · -- μ(Cᶜ) = 0 means μ(C) = 1, and since μ(C) ≤ δ, we have 1 ≤ δ
    push_neg at hCc_pos
    have hCc0 := le_antisymm hCc_pos (zero_le _)
    refine ⟨∅, MeasurableSet.empty, by simp [hδ.le], ?_⟩
    have : μ Set.univ ≤ δ := by
      calc μ Set.univ = μ C + μ Cᶜ := by
            rw [← measure_add_measure_compl hC_meas]
        _ = μ C + 0 := by rw [hCc0]
        _ = μ C := add_zero _
        _ ≤ δ := hC_small
    calc μ (basin T ∅)ᶜ ≤ μ Set.univ := measure_mono (subset_univ _)
      _ ≤ δ := this

/-! ### Basin complement contained in small invariant set -/

/-- If basin T A covers Cᶜ a.e. (where C is a.e. invariant), then
    (basin T A)ᶜ ⊆ᵃᵉ C. -/
theorem basin_compl_subset_ae_of_covers_complement
    (μ : Measure Ω) [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ)
    {A C : Set Ω} (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hC_inv : C =ᵐ[μ] T ⁻¹' C)
    (h_covers : μ (Cᶜ \ basin T A) = 0) :
    μ (basin T A)ᶜ ≤ μ C := by
  calc μ (basin T A)ᶜ
      ≤ μ (C ∪ (Cᶜ \ basin T A)) := by
        apply measure_mono; intro x hx; by_cases hxC : x ∈ C
        · exact Or.inl hxC
        · exact Or.inr ⟨hxC, hx⟩
    _ ≤ μ C + μ (Cᶜ \ basin T A) := measure_union_le _ _
    _ = μ C + 0 := by rw [h_covers]
    _ = μ C := add_zero _

end Submission.InvariantSigmaAlgebra

end
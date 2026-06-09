import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.RokhlinCore
import Submission.BasinCoverage
import Submission.CondExpInvariant
import Submission.ErgodicDecomp
import Submission.GeneralBasin
import Submission.BasinCondExp

/-!
# Localized basin coverage and the zero-infimum reduction

This file provides:
1. A localized version of the positive-infimum basin coverage theorem
   (within an invariant subset rather than the full space).
2. The `basin_full_of_condExp_pos` bridge from `BasinCondExp.lean` as API.
3. A Zorn-based maximal invariant set lemma.

## Main results

* `exists_small_set_covering_invariant` — localized basin coverage from an ergodic covering
* `exists_small_marker_covering_invariant` — localized positive-infimum basin coverage
-/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Submission.RokhlinCore Submission.BasinCoverage Submission.CondExpInvariant
open Submission.ErgodicDecomp Submission.GeneralBasin Submission.BasinCondExp
open Classical

noncomputable section

namespace Submission.ZornInvariant

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-! ### Localized basin coverage -/

/-
Localized version of `exists_small_set_large_basin_of_covering`:
    within an invariant set C covered by ergodic pieces, find a marker
    of small measure whose basin covers C a.e.
-/
set_option maxHeartbeats 800000 in
theorem exists_small_set_covering_invariant
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {C : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < μ C)
    (hCinv : C =ᵐ[μ] T ⁻¹' C)
    {δ : ENNReal} (hδ : 0 < δ)
    (E : ℕ → Set Ω)
    (hE_meas : ∀ k, MeasurableSet (E k))
    (hE_sub : ∀ k, E k ⊆ C)
    (hE_erg : ∀ k, 0 < μ (E k) → IsErgodicOn μ T (E k))
    (hE_disj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hE_cover : μ (C \ ⋃ k, E k) = 0) :
    ∃ A : Set Ω, MeasurableSet A ∧ A ⊆ C ∧ μ A ≤ δ ∧ μ (C \ basin T A) = 0 := by
  -- Set A = ⋃ k, A_k.
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set Ω, (∀ k, MeasurableSet (A k)) ∧ (∀ k, A k ⊆ E k) ∧ (∀ k, μ (A k) ≤ δ * (1 / 2) ^ (k + 1)) ∧ (∀ k, μ (E k \ basin T (A k)) = 0) := by
    have hA_k : ∀ k, ∃ A_k : Set Ω, MeasurableSet A_k ∧ A_k ⊆ E k ∧ μ A_k ≤ δ * (1 / 2) ^ (k + 1) ∧ μ (E k \ basin T A_k) = 0 := by
      intro k
      by_cases hEk : 0 < μ (E k);
      · obtain ⟨A_k, hA_k_meas, hA_k_sub, hA_k_pos, hA_k_small⟩ : ∃ A_k : Set Ω, MeasurableSet A_k ∧ A_k ⊆ E k ∧ 0 < μ A_k ∧ μ A_k ≤ δ * (1 / 2) ^ (k + 1) := by
          convert exists_small_measurableSet_subset μ ( hE_meas k ) hEk ( show 0 < δ * ( 1 / 2 ) ^ ( k + 1 ) from ENNReal.mul_pos hδ.ne' ( by simp +decide ) ) using 1;
          exact?;
        exact ⟨ A_k, hA_k_meas, hA_k_sub, hA_k_small, IsErgodicOn.basin_full hT ( hE_erg k hEk ) hEk hA_k_meas hA_k_sub hA_k_pos ⟩;
      · refine' ⟨ ∅, _, _, _, _ ⟩ <;> simp_all +decide [ Set.diff_eq ];
        exact MeasureTheory.measure_mono_null ( fun x hx => hx.1 ) hEk;
    exact ⟨ fun k => Classical.choose ( hA_k k ), fun k => Classical.choose_spec ( hA_k k ) |>.1, fun k => Classical.choose_spec ( hA_k k ) |>.2.1, fun k => Classical.choose_spec ( hA_k k ) |>.2.2.1, fun k => Classical.choose_spec ( hA_k k ) |>.2.2.2 ⟩;
  refine' ⟨ ⋃ k, A k, MeasurableSet.iUnion hA.1, _, _, _ ⟩;
  · exact Set.iUnion_subset fun k => Set.Subset.trans ( hA.2.1 k ) ( hE_sub k );
  · refine' le_trans ( MeasureTheory.measure_iUnion_le _ ) _;
    refine' le_trans ( ENNReal.tsum_le_tsum hA.2.2.1 ) _;
    ring_nf;
    rw [ ENNReal.tsum_mul_left, ENNReal.tsum_geometric ] ; norm_num;
    rw [ mul_assoc, ENNReal.inv_mul_cancel ] <;> norm_num;
  · have h_union : C \ basin T (⋃ k, A k) ⊆ (C \ ⋃ k, E k) ∪ ⋃ k, (E k \ basin T (A k)) := by
      intro x hx;
      by_cases hx' : x ∈ ⋃ k, E k <;> simp_all +decide [ basin ];
    exact MeasureTheory.measure_mono_null h_union ( MeasureTheory.measure_union_null hE_cover ( MeasureTheory.measure_iUnion_null fun k => hA.2.2.2 k ) )

/-
Localized positive-infimum basin coverage: within an invariant set C
    where every positive-measure invariant subset has measure ≥ α > 0,
    find a small marker whose basin covers C a.e.
-/
set_option maxHeartbeats 1600000 in
theorem exists_small_marker_covering_invariant
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {C : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < μ C)
    (hCinv : C =ᵐ[μ] T ⁻¹' C)
    {δ : ENNReal} (hδ : 0 < δ)
    (α : ENNReal) (hα : 0 < α)
    (hα_bound : ∀ F : Set Ω, MeasurableSet F → F ⊆ C → F =ᵐ[μ] T ⁻¹' F →
      0 < μ F → α ≤ μ F) :
    ∃ A : Set Ω, MeasurableSet A ∧ A ⊆ C ∧ μ A ≤ δ ∧ μ (C \ basin T A) = 0 := by
  by_contra! h_contra';
  -- Let $E$ be a maximal finite family of disjoint ergodic subsets of $C$.
  obtain ⟨E, hE_meas, hE_disj, hE_erg⟩ : ∃ E : Finset (Set Ω), (∀ A ∈ E, MeasurableSet A ∧ A ⊆ C ∧ A =ᵐ[μ] T ⁻¹' A ∧ 0 < μ A ∧ IsErgodicOn μ T A) ∧ (∀ A ∈ E, ∀ B ∈ E, A ≠ B → Disjoint A B) ∧ (∀ A : Set Ω, MeasurableSet A → A ⊆ C → A =ᵐ[μ] T ⁻¹' A → 0 < μ A → IsErgodicOn μ T A → ∃ B ∈ E, ¬ Disjoint A B) := by
    have h_max_family : ∃ E : Finset (Set Ω), (∀ A ∈ E, MeasurableSet A ∧ A ⊆ C ∧ A =ᵐ[μ] T ⁻¹' A ∧ 0 < μ A ∧ IsErgodicOn μ T A) ∧ (∀ A ∈ E, ∀ B ∈ E, A ≠ B → Disjoint A B) ∧ ∀ F : Finset (Set Ω), (∀ A ∈ F, MeasurableSet A ∧ A ⊆ C ∧ A =ᵐ[μ] T ⁻¹' A ∧ 0 < μ A ∧ IsErgodicOn μ T A) → (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) → F.card ≤ E.card := by
      have h_max_family : ∃ E : Finset (Set Ω), (∀ A ∈ E, MeasurableSet A ∧ A ⊆ C ∧ A =ᵐ[μ] T ⁻¹' A ∧ 0 < μ A ∧ IsErgodicOn μ T A) ∧ (∀ A ∈ E, ∀ B ∈ E, A ≠ B → Disjoint A B) ∧ ∀ F : Finset (Set Ω), (∀ A ∈ F, MeasurableSet A ∧ A ⊆ C ∧ A =ᵐ[μ] T ⁻¹' A ∧ 0 < μ A ∧ IsErgodicOn μ T A) → (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) → F.card ≤ E.card := by
        have h_finite : Set.Finite {n : ℕ | ∃ F : Finset (Set Ω), (∀ A ∈ F, MeasurableSet A ∧ A ⊆ C ∧ A =ᵐ[μ] T ⁻¹' A ∧ 0 < μ A ∧ IsErgodicOn μ T A) ∧ (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) ∧ F.card = n} := by
          refine' Set.finite_iff_bddAbove.mpr ⟨ ⌊ ( μ C |> ENNReal.toReal ) / α.toReal⌋₊, fun n hn => _ ⟩
          obtain ⟨ F, hF₁, hF₂, rfl ⟩ := hn
          have h_card : F.card * α ≤ μ C := by
            have h_card : ∑ A ∈ F, μ A ≤ μ C := by
              rw [ ← MeasureTheory.measure_biUnion_finset ];
              · exact MeasureTheory.measure_mono ( Set.iUnion₂_subset fun A hA => hF₁ A hA |>.2.1 );
              · exact fun A hA B hB hAB => hF₂ A hA B hB hAB;
              · exact fun A hA => hF₁ A hA |>.1;
            refine' le_trans _ h_card;
            exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun x hx => hα_bound x ( hF₁ x hx |>.1 ) ( hF₁ x hx |>.2.1 ) ( hF₁ x hx |>.2.2.1 ) ( hF₁ x hx |>.2.2.2.1 ) )
          have h_card_real : (F.card : ℝ) * α.toReal ≤ (μ C).toReal := by
            convert ENNReal.toReal_mono _ h_card using 1 <;> norm_num [ hα.ne' ]
          have h_card_floor : (F.card : ℝ) ≤ ⌊ ( μ C |> ENNReal.toReal ) / α.toReal⌋₊ := by
            exact_mod_cast Nat.le_floor ( by rwa [ le_div_iff₀ ( ENNReal.toReal_pos hα.ne' ( by aesop ) ) ] )
          exact_mod_cast h_card_floor
        obtain ⟨n, hn⟩ : ∃ n ∈ {n : ℕ | ∃ F : Finset (Set Ω), (∀ A ∈ F, MeasurableSet A ∧ A ⊆ C ∧ A =ᵐ[μ] T ⁻¹' A ∧ 0 < μ A ∧ IsErgodicOn μ T A) ∧ (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) ∧ F.card = n}, ∀ m ∈ {n : ℕ | ∃ F : Finset (Set Ω), (∀ A ∈ F, MeasurableSet A ∧ A ⊆ C ∧ A =ᵐ[μ] T ⁻¹' A ∧ 0 < μ A ∧ IsErgodicOn μ T A) ∧ (∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B) ∧ F.card = n}, n ≥ m := by
          apply_rules [ Set.exists_max_image ];
          exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
        rcases hn.1 with ⟨ E, hE₁, hE₂, rfl ⟩ ; exact ⟨ E, hE₁, hE₂, fun F hF₁ hF₂ => hn.2 _ ⟨ F, hF₁, hF₂, rfl ⟩ ⟩ ;
      exact h_max_family;
    obtain ⟨ E, hE₁, hE₂, hE₃ ⟩ := h_max_family; use E; refine' ⟨ hE₁, hE₂, _ ⟩ ; intro A hA₁ hA₂ hA₃ hA₄ hA₅; contrapose! hE₃;
    refine' ⟨ Insert.insert A E, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_insert_of_notMem ];
    · exact fun B hB hBA => Disjoint.symm ( hE₃ B hB );
    · rw [ Finset.card_insert_of_notMem ] ; aesop;
      intro hA₆; specialize hE₃ A hA₆; simp_all +decide [ Set.disjoint_left ] ;
      simpa using hE₁ _ hA₆ |>.2.2.2.1.ne';
  -- The union of E covers C a.e.
  have hE_cover : μ (C \ ⋃ A ∈ E, A) = 0 := by
    by_contra h_contra'';
    -- Let $F$ be an ergodic subset of $C \setminus \bigcup_{A \in E} A$.
    obtain ⟨F, hF_meas, hF_sub, hF_erg⟩ : ∃ F : Set Ω, MeasurableSet F ∧ F ⊆ C \ ⋃ A ∈ E, A ∧ F =ᵐ[μ] T ⁻¹' F ∧ 0 < μ F ∧ IsErgodicOn μ T F := by
      have hF_meas : MeasurableSet (C \ ⋃ A ∈ E, A) := by
        exact hC.diff ( MeasurableSet.biUnion ( Finset.countable_toSet E ) fun A hA => hE_meas A hA |>.1 );
      apply exists_ergodicOn_subset_of_pos_infimum;
      any_goals assumption;
      · exact pos_iff_ne_zero.mpr h_contra'';
      · have hF_inv : ∀ A ∈ E, A =ᵐ[μ] T ⁻¹' A := by
          exact fun A hA => hE_meas A hA |>.2.2.1;
        have hF_inv : (⋃ A ∈ E, A) =ᵐ[μ] T ⁻¹' (⋃ A ∈ E, A) := by
          have hF_inv : ∀ {S : Finset (Set Ω)}, (∀ A ∈ S, A =ᵐ[μ] T ⁻¹' A) → ⋃ A ∈ S, A =ᵐ[μ] T ⁻¹' (⋃ A ∈ S, A) := by
            intros S hS; induction S using Finset.induction <;> simp_all +decide [ Set.preimage_union ] ;
            exact Filter.EventuallyEq.union hS.1 ‹_›;
          exact hF_inv ‹_›;
        convert ae_invariant_diff μ hCinv hF_inv using 1;
      · exact fun F hF_meas hF_sub hF_inv hF_pos => hα_bound F hF_meas ( fun x hx => hF_sub hx |>.1 ) hF_inv hF_pos;
    obtain ⟨ B, hB₁, hB₂ ⟩ := hE_erg F hF_meas ( fun x hx => hF_sub hx |>.1 ) hF_erg.1 hF_erg.2.1 hF_erg.2.2;
    exact hB₂ ( Set.disjoint_left.mpr fun x hx₁ hx₂ => hF_sub hx₁ |>.2 <| Set.mem_iUnion₂.mpr ⟨ B, hB₁, hx₂ ⟩ );
  -- Enumerate the finite collection as a sequence (padding with ∅).
  obtain ⟨E_seq, hE_seq⟩ : ∃ E_seq : ℕ → Set Ω, (∀ k, MeasurableSet (E_seq k)) ∧ (∀ k, E_seq k ⊆ C) ∧ (∀ k, 0 < μ (E_seq k) → IsErgodicOn μ T (E_seq k)) ∧ Pairwise (fun i j => Disjoint (E_seq i) (E_seq j)) ∧ μ (C \ ⋃ k, E_seq k) = 0 := by
    -- Enumerate the finite collection as a sequence (padding with ∅) and show that it satisfies the required properties.
    obtain ⟨E_seq, hE_seq⟩ : ∃ E_seq : Fin E.card → Set Ω, (∀ k, MeasurableSet (E_seq k)) ∧ (∀ k, E_seq k ⊆ C) ∧ (∀ k, 0 < μ (E_seq k) → IsErgodicOn μ T (E_seq k)) ∧ Pairwise (fun i j => Disjoint (E_seq i) (E_seq j)) ∧ ⋃ A ∈ E, A = ⋃ k, E_seq k := by
      obtain ⟨E_seq, hE_seq⟩ : ∃ E_seq : Fin E.card → Set Ω, (∀ k, E_seq k ∈ E) ∧ (∀ k l, k ≠ l → E_seq k ≠ E_seq l) ∧ ⋃ A ∈ E, A = ⋃ k, E_seq k := by
        have hE_seq : ∃ E_seq : Fin E.card → Set Ω, (∀ k, E_seq k ∈ E) ∧ (∀ k l, k ≠ l → E_seq k ≠ E_seq l) ∧ ∀ A ∈ E, ∃ k, E_seq k = A := by
          have hE_seq : Nonempty (Fin E.card ≃ E) := by
            exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
          exact ⟨ _, fun k => hE_seq.some k |>.2, fun k l hkl => fun h => hkl <| hE_seq.some.injective <| Subtype.ext h, fun A hA => ⟨ hE_seq.some.symm ⟨ A, hA ⟩, by simp +decide ⟩ ⟩;
        obtain ⟨ E_seq, hE_seq₁, hE_seq₂, hE_seq₃ ⟩ := hE_seq; use E_seq; simp +decide [ hE_seq₁, hE_seq₂, hE_seq₃ ] ;
        exact ⟨ hE_seq₂, by ext x; exact ⟨ fun hx => by rcases Set.mem_iUnion₂.1 hx with ⟨ A, hA, hx ⟩ ; obtain ⟨ k, rfl ⟩ := hE_seq₃ A hA; exact Set.mem_iUnion.2 ⟨ k, hx ⟩, fun hx => by rcases Set.mem_iUnion.1 hx with ⟨ k, hk ⟩ ; exact Set.mem_iUnion₂.2 ⟨ _, hE_seq₁ k, hk ⟩ ⟩ ⟩;
      exact ⟨ E_seq, fun k => hE_meas _ ( hE_seq.1 k ) |>.1, fun k => hE_meas _ ( hE_seq.1 k ) |>.2.1, fun k hk => hE_meas _ ( hE_seq.1 k ) |>.2.2.2.2, fun i j hij => hE_disj _ ( hE_seq.1 i ) _ ( hE_seq.1 j ) ( hE_seq.2.1 i j hij ), hE_seq.2.2 ⟩;
    refine' ⟨ fun k => if hk : k < E.card then E_seq ⟨ k, hk ⟩ else ∅, _, _, _, _, _ ⟩ <;> simp +decide [ *, Pairwise ];
    · intro k; split_ifs <;> simp +decide [ * ] ;
    · intro k; split_ifs <;> simp +decide [ *, Set.subset_def ] ;
    · intro k hk; split_ifs at hk ⊢ <;> simp_all +decide ;
    · intro i j hij; split_ifs <;> simp_all +decide [ Pairwise ] ;
    · convert hE_cover using 2;
      ext x; simp [hE_seq];
      exact fun _ => ⟨ fun h i => h i.val |> fun hi => by simpa [ i.2 ] using hi, fun h i => by split_ifs <;> [ exact h ⟨ i, by linarith ⟩ ; exact by simp +decide ] ⟩;
  exact h_contra' _ ( exists_small_set_covering_invariant μ T hT hap hC hCpos hCinv hδ E_seq hE_seq.1 hE_seq.2.1 hE_seq.2.2.1 hE_seq.2.2.2.1 hE_seq.2.2.2.2 |> Classical.choose_spec |> And.left ) ( exists_small_set_covering_invariant μ T hT hap hC hCpos hCinv hδ E_seq hE_seq.1 hE_seq.2.1 hE_seq.2.2.1 hE_seq.2.2.2.1 hE_seq.2.2.2.2 |> Classical.choose_spec |> And.right |> And.left ) ( exists_small_set_covering_invariant μ T hT hap hC hCpos hCinv hδ E_seq hE_seq.1 hE_seq.2.1 hE_seq.2.2.1 hE_seq.2.2.2.1 hE_seq.2.2.2.2 |> Classical.choose_spec |> And.right |> And.right |> And.left ) ( exists_small_set_covering_invariant μ T hT hap hC hCpos hCinv hδ E_seq hE_seq.1 hE_seq.2.1 hE_seq.2.2.1 hE_seq.2.2.2.1 hE_seq.2.2.2.2 |> Classical.choose_spec |> And.right |> And.right |> And.right )

end Submission.ZornInvariant

end
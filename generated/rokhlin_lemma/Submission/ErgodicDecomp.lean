import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.RokhlinCore
import Submission.BasinCoverage

/-! ## Ergodic decomposition infrastructure -/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Submission.RokhlinCore Submission.BasinCoverage
open Classical

noncomputable section

namespace Submission.ErgodicDecomp

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Definition of IsErgodicOn -/

structure IsErgodicOn (μ : Measure Ω) (T : Ω → Ω) (C : Set Ω) : Prop where
  measurable : MeasurableSet C
  ae_invariant : C =ᵐ[μ] T ⁻¹' C
  dichotomy : ∀ D : Set Ω, MeasurableSet D → D ⊆ C →
    D =ᵐ[μ] T ⁻¹' D → μ D = 0 ∨ μ (C \ D) = 0

/-! ### Basic API -/

theorem IsErgodicOn.basin_full {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ)
    {C : Set Ω} (herg : IsErgodicOn μ T C) (hCpos : 0 < μ C)
    {A : Set Ω} (hA : MeasurableSet A) (hAC : A ⊆ C) (hApos : 0 < μ A) :
    μ (C \ basin T A) = 0 :=
  ergodic_on_basin_full μ hT herg.measurable hCpos herg.ae_invariant
    herg.dichotomy hA hAC hApos

theorem not_ergodicOn_split {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ)
    {C : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < μ C)
    (hCinv : C =ᵐ[μ] T ⁻¹' C)
    (hnoterg : ¬ IsErgodicOn μ T C) :
    ∃ D : Set Ω, MeasurableSet D ∧ D ⊆ C ∧
      D =ᵐ[μ] T ⁻¹' D ∧ 0 < μ D ∧ 0 < μ (C \ D) := by
  apply exists_invariant_split μ hT hC hCpos hCinv
  intro h; exact hnoterg ⟨hC, hCinv, h⟩

/-! ### The infimum lemma -/

theorem ergodicOn_of_measure_lt_double_infimum
    {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ)
    {C D : Set Ω}
    (hD : MeasurableSet D) (hDC : D ⊆ C) (hDinv : D =ᵐ[μ] T ⁻¹' D)
    (hDpos : 0 < μ D)
    (α : ENNReal) (hα : 0 < α)
    (hα_bound : ∀ E : Set Ω, MeasurableSet E → E ⊆ C → E =ᵐ[μ] T ⁻¹' E →
      0 < μ E → α ≤ μ E)
    (hD_small : μ D < 2 * α) :
    IsErgodicOn μ T D := by
  refine ⟨hD, hDinv, fun E hE hED hEinv => ?_⟩
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  have hEpos : 0 < μ E := lt_of_le_of_ne (zero_le _) (Ne.symm h1)
  have hDEpos : 0 < μ (D \ E) := lt_of_le_of_ne (zero_le _) (Ne.symm h2)
  have hDEinv : (D \ E) =ᵐ[μ] T ⁻¹' (D \ E) := by
    rw [Set.preimage_diff]; exact hDinv.diff hEinv
  have hE_ge : α ≤ μ E := hα_bound E hE (hED.trans hDC) hEinv hEpos
  have hDE_ge : α ≤ μ (D \ E) :=
    hα_bound (D \ E) (hD.diff hE) (diff_subset.trans hDC) hDEinv hDEpos
  have hsum : μ E + μ (D \ E) ≤ μ D := by
    have : E ∪ D \ E = D := Set.union_diff_cancel hED
    rw [← measure_union disjoint_sdiff_right (hD.diff hE), this]
  have : 2 * α ≤ μ D := le_trans (by rw [two_mul]; exact add_le_add hE_ge hDE_ge) hsum
  exact absurd hD_small (not_lt.mpr this)

/-! ### Ergodic subset existence -/

theorem exists_ergodicOn_subset_of_pos_infimum
    {μ : Measure Ω} [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ)
    {C : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < μ C)
    (hCinv : C =ᵐ[μ] T ⁻¹' C)
    (α : ENNReal) (hα : 0 < α)
    (hα_bound : ∀ E : Set Ω, MeasurableSet E → E ⊆ C → E =ᵐ[μ] T ⁻¹' E →
      0 < μ E → α ≤ μ E) :
    ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ C ∧ E =ᵐ[μ] T ⁻¹' E ∧ 0 < μ E ∧
      IsErgodicOn μ T E := by
  by_contra! h;
  -- By induction, we can construct a sequence of subsets $D_n \subseteq C$ such that $\mu(D_n) \leq \mu(C) - n\alpha$.
  have h_seq : ∀ n : ℕ, ∃ D : Set Ω, MeasurableSet D ∧ D ⊆ C ∧ D =ᵐ[μ] T ⁻¹' D ∧ 0 < μ D ∧ μ D ≤ μ C - n * α := by
    intro n
    induction' n with n ih;
    · exact ⟨ C, hC, Set.Subset.refl _, hCinv, hCpos, by simp +decide ⟩;
    · obtain ⟨ D, hD₁, hD₂, hD₃, hD₄, hD₅ ⟩ := ih;
      -- Since $D$ is not ergodic, there exists a subset $E \subseteq D$ such that $E$ is measurable, $E \subseteq D$, $E =ᵐ[μ] T ⁻¹' E$, $0 < μ E$, and $0 < μ (D \ E)$.
      obtain ⟨ E, hE₁, hE₂, hE₃, hE₄, hE₅ ⟩ : ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ D ∧ E =ᵐ[μ] T ⁻¹' E ∧ 0 < μ E ∧ 0 < μ (D \ E) := by
        apply not_ergodicOn_split;
        · exact hT;
        · exact hD₁;
        · exact hD₄;
        · exact hD₃;
        · exact h D hD₁ hD₂ hD₃ hD₄;
      refine' ⟨ D \ E, _, _, _, _, _ ⟩;
      · exact hD₁.diff hE₁;
      · exact fun x hx => hD₂ hx.1;
      · filter_upwards [ hD₃, hE₃ ] with x hx₁ hx₂ ; simp_all +decide [ Set.preimage ];
        exact ⟨ fun hx => ⟨ hx₁.mp hx.1, fun hx' => hx.2 <| hx₂.mpr hx' ⟩, fun hx => ⟨ hx₁.mpr hx.1, fun hx' => hx.2 <| hx₂.mp hx' ⟩ ⟩;
      · exact hE₅;
      · have h_measure_D_minus_E : μ (D \ E) = μ D - μ E := by
          rw [ MeasureTheory.measure_diff ] <;> norm_num [ hD₁, hE₁, hE₂ ];
        rw [ h_measure_D_minus_E, Nat.cast_succ, add_mul, one_mul, ← tsub_tsub ];
        exact tsub_le_tsub hD₅ ( hα_bound E hE₁ ( hE₂.trans hD₂ ) hE₃ hE₄ );
  obtain ⟨ n, hn ⟩ := ENNReal.exists_nat_mul_gt hα.ne' ( MeasureTheory.measure_ne_top μ C );
  obtain ⟨ D, hD₁, hD₂, hD₃, hD₄, hD₅ ⟩ := h_seq n; exact hD₄.ne' ( le_antisymm ( le_trans hD₅ ( tsub_eq_zero_of_le hn.le |> le_of_eq ) ) ( zero_le _ ) ) ;

/-! ### Basin coverage from ergodic covering -/

theorem exists_small_set_large_basin_of_covering
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {δ : ENNReal} (hδ : 0 < δ)
    (E : ℕ → Set Ω)
    (hE_meas : ∀ k, MeasurableSet (E k))
    (hE_erg : ∀ k, 0 < μ (E k) → IsErgodicOn μ T (E k))
    (hE_disj : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hE_cover : μ (Set.univ \ ⋃ k, E k) = 0) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A ≤ δ ∧ μ (basin T A)ᶜ ≤ δ := by
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
    suffices h : μ (basin T (⋃ k, Ak k))ᶜ = 0 by rw [h]; exact zero_le _
    rw [compl_eq_univ_diff, basin_iUnion]
    apply le_antisymm _ (zero_le _)
    have h_subset : Set.univ \ ⋃ k, basin T (Ak k) ⊆
        (Set.univ \ ⋃ k, E k) ∪ ⋃ k, (E k \ basin T (Ak k)) := by
      intro x hx
      simp only [mem_diff, mem_univ, true_and, mem_iUnion, mem_union] at *
      by_cases hxE : ∃ k, x ∈ E k
      · obtain ⟨k, hk⟩ := hxE
        right; exact ⟨k, hk, fun h' => hx ⟨k, h'⟩⟩
      · left; exact hxE
    calc μ (Set.univ \ ⋃ k, basin T (Ak k))
        ≤ μ ((Set.univ \ ⋃ k, E k) ∪ ⋃ k, (E k \ basin T (Ak k))) :=
          measure_mono h_subset
      _ ≤ μ (Set.univ \ ⋃ k, E k) + μ (⋃ k, (E k \ basin T (Ak k))) :=
          measure_union_le _ _
      _ = 0 + μ (⋃ k, (E k \ basin T (Ak k))) := by rw [hE_cover]
      _ ≤ 0 + ∑' k, μ (E k \ basin T (Ak k)) :=
          add_le_add_right (measure_iUnion_le _) _
      _ = 0 := by simp [hAk_basin]

/-! ### Ergodic covering when infimum is positive -/

/-- Complement of a.e. invariant set is a.e. invariant -/
theorem ae_invariant_compl {T : Ω → Ω} (μ : Measure Ω) [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ)
    {C : Set Ω} (hC : MeasurableSet C) (hCinv : C =ᵐ[μ] T ⁻¹' C) :
    Cᶜ =ᵐ[μ] T ⁻¹' Cᶜ := hCinv.compl

/-- Difference of a.e. invariant sets is a.e. invariant -/
theorem ae_invariant_diff {T : Ω → Ω} (μ : Measure Ω)
    {C D : Set Ω} (hCinv : C =ᵐ[μ] T ⁻¹' C) (hDinv : D =ᵐ[μ] T ⁻¹' D) :
    (C \ D) =ᵐ[μ] T ⁻¹' (C \ D) := by
  rw [Set.preimage_diff]; exact hCinv.diff hDinv

/-
When every positive-measure invariant set has measure ≥ α > 0,
    a maximal disjoint family of ergodic pieces covers Ω a.e.
-/
set_option maxHeartbeats 800000 in
theorem exists_ergodic_covering_of_pos_infimum
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    (α : ENNReal) (hα : 0 < α)
    (hα_bound : ∀ E : Set Ω, MeasurableSet E → E =ᵐ[μ] T ⁻¹' E →
      0 < μ E → α ≤ μ E) :
    ∃ E : ℕ → Set Ω,
      (∀ k, MeasurableSet (E k)) ∧
      (∀ k, 0 < μ (E k) → IsErgodicOn μ T (E k)) ∧
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      μ (Set.univ \ ⋃ k, E k) = 0 := by
  have h_exists_ergodic_subset : ∀ (C : Set Ω), MeasurableSet C → C =ᵐ[μ] T ⁻¹' C → 0 < μ C → ∃ E : Set Ω, MeasurableSet E ∧ E ⊆ C ∧ E =ᵐ[μ] T ⁻¹' E ∧ 0 < μ E ∧ IsErgodicOn μ T E := by
    intros C hC hCinv hCpos
    by_contra h_no_ergodic_subset;
    apply_rules [ exists_ergodicOn_subset_of_pos_infimum ];
    exact fun E hE hEC hEinv hEpos => hα_bound E hE hEinv hEpos;
  have h_finite_union : ∀ (C : Set Ω), MeasurableSet C → C =ᵐ[μ] T ⁻¹' C → 0 < μ C → ∃ E : Finset (Set Ω), (∀ e ∈ E, MeasurableSet e ∧ e ⊆ C ∧ e =ᵐ[μ] T ⁻¹' e ∧ 0 < μ e ∧ IsErgodicOn μ T e) ∧ (∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧ μ (C \ ⋃ e ∈ E, e) = 0 := by
    intro C hC hCinv hCpos
    by_contra h_contra;
    obtain ⟨E, hE⟩ : ∃ E : Finset (Set Ω), (∀ e ∈ E, MeasurableSet e ∧ e ⊆ C ∧ e =ᵐ[μ] T ⁻¹' e ∧ 0 < μ e ∧ IsErgodicOn μ T e) ∧ (∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧ ∀ F : Finset (Set Ω), (∀ e ∈ F, MeasurableSet e ∧ e ⊆ C ∧ e =ᵐ[μ] T ⁻¹' e ∧ 0 < μ e ∧ IsErgodicOn μ T e) → (∀ e₁ ∈ F, ∀ e₂ ∈ F, e₁ ≠ e₂ → Disjoint e₁ e₂) → F.card ≤ E.card := by
      have h_finite_union : Set.Finite {n : ℕ | ∃ E : Finset (Set Ω), (∀ e ∈ E, MeasurableSet e ∧ e ⊆ C ∧ e =ᵐ[μ] T ⁻¹' e ∧ 0 < μ e ∧ IsErgodicOn μ T e) ∧ (∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧ E.card = n} := by
        refine' Set.finite_iff_bddAbove.mpr ⟨ ⌊ ( μ C |> ENNReal.toReal ) / α.toReal⌋₊, fun n hn => _ ⟩;
        obtain ⟨ E, hE₁, hE₂, rfl ⟩ := hn;
        have h_sum_measure : ∑ e ∈ E, μ e ≤ μ C := by
          rw [ ← MeasureTheory.measure_biUnion_finset ];
          · exact MeasureTheory.measure_mono ( Set.iUnion₂_subset fun e he => hE₁ e he |>.2.1 );
          · exact fun x hx y hy hxy => hE₂ x hx y hy hxy;
          · exact fun e he => hE₁ e he |>.1;
        have h_sum_measure : ∑ e ∈ E, μ e ≥ E.card * α := by
          exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun e he => hα_bound e ( hE₁ e he |>.1 ) ( hE₁ e he |>.2.2.1 ) ( hE₁ e he |>.2.2.2.1 ) );
        refine' Nat.le_floor _;
        rw [ le_div_iff₀ ] <;> norm_cast;
        · convert ENNReal.toReal_mono _ ( h_sum_measure.trans ‹_› ) using 1;
          · rw [ ENNReal.toReal_mul, ENNReal.toReal_natCast ];
          · exact MeasureTheory.measure_ne_top _ _;
        · exact ENNReal.toReal_pos hα.ne' (by
          rintro rfl; simp +decide at *;
          exact absurd ( hα_bound C hC hCinv ) hCpos.ne');
      obtain ⟨n, hn⟩ : ∃ n ∈ {n : ℕ | ∃ E : Finset (Set Ω), (∀ e ∈ E, MeasurableSet e ∧ e ⊆ C ∧ e =ᵐ[μ] T ⁻¹' e ∧ 0 < μ e ∧ IsErgodicOn μ T e) ∧ (∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧ E.card = n}, ∀ m ∈ {n : ℕ | ∃ E : Finset (Set Ω), (∀ e ∈ E, MeasurableSet e ∧ e ⊆ C ∧ e =ᵐ[μ] T ⁻¹' e ∧ 0 < μ e ∧ IsErgodicOn μ T e) ∧ (∀ e₁ ∈ E, ∀ e₂ ∈ E, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧ E.card = n}, n ≥ m := by
        apply_rules [ Set.exists_max_image ];
        exact ⟨ 0, ⟨ ∅, by simp +decide ⟩ ⟩;
      rcases hn.1 with ⟨ E, hE₁, hE₂, rfl ⟩ ; exact ⟨ E, hE₁, hE₂, fun F hF₁ hF₂ => hn.2 _ ⟨ F, hF₁, hF₂, rfl ⟩ ⟩ ;
    have h_remainder : C \ ⋃ e ∈ E, e =ᵐ[μ] T ⁻¹' (C \ ⋃ e ∈ E, e) := by
      have h_remainder : ⋃ e ∈ E, e =ᵐ[μ] T ⁻¹' (⋃ e ∈ E, e) := by
        have h_remainder : ∀ e ∈ E, e =ᵐ[μ] T ⁻¹' e := by
          exact fun e he => hE.1 e he |>.2.2.1;
        have h_remainder : ∀ {F : Finset (Set Ω)}, (∀ e ∈ F, e =ᵐ[μ] T ⁻¹' e) → (⋃ e ∈ F, e) =ᵐ[μ] T ⁻¹' (⋃ e ∈ F, e) := by
          intros F hF; induction' F using Finset.induction with e F ih; simp +decide [ * ] ;
          simp +zetaDelta at *;
          exact Filter.EventuallyEq.union hF.1 ( by rename_i h; exact h hF.2 );
        exact h_remainder ‹_›;
      convert ae_invariant_diff μ hCinv h_remainder using 1;
    obtain ⟨E', hE'⟩ : ∃ E' : Set Ω, MeasurableSet E' ∧ E' ⊆ C \ ⋃ e ∈ E, e ∧ E' =ᵐ[μ] T ⁻¹' E' ∧ 0 < μ E' ∧ IsErgodicOn μ T E' := by
      apply h_exists_ergodic_subset;
      · exact hC.diff ( MeasurableSet.biUnion ( Finset.countable_toSet E ) fun e he => hE.1 e he |>.1 );
      · exact h_remainder;
      · exact lt_of_le_of_ne ( zero_le _ ) ( Ne.symm fun h => h_contra ⟨ E, hE.1, hE.2.1, h ⟩ );
    have := hE.2.2 ( Insert.insert E' E ) ?_ ?_;
    · rw [ Finset.card_insert_of_notMem ] at this <;> norm_num at this;
      exact fun h => hE'.2.2.2.1.ne' ( MeasureTheory.measure_mono_null ( fun x hx => by have := hE'.2.1 hx; aesop ) ( MeasureTheory.measure_empty ) );
    · grind;
    · simp +zetaDelta at *;
      exact ⟨ fun e he he' => Set.disjoint_left.mpr fun x hx hx' => by have := hE'.2.1 hx; aesop, fun e he => ⟨ fun he' => Set.disjoint_left.mpr fun x hx hx' => by have := hE'.2.1 hx'; aesop, fun e' he' he'' => hE.2.1 e he e' he' he'' ⟩ ⟩;
  obtain ⟨ E, hE₁, hE₂, hE₃ ⟩ := h_finite_union Set.univ MeasurableSet.univ ( by simp +decide [ Filter.EventuallyEq ] ) ( by simp +decide );
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Set Ω, (∀ k, f k ∈ E ∪ {∅}) ∧ (∀ k₁ k₂, k₁ ≠ k₂ → Disjoint (f k₁) (f k₂)) ∧ ⋃ k, f k = ⋃ e ∈ E, e := by
    obtain ⟨f, hf⟩ : ∃ f : Fin (E.card) → Set Ω, (∀ k, f k ∈ E) ∧ (∀ k₁ k₂, k₁ ≠ k₂ → Disjoint (f k₁) (f k₂)) ∧ ⋃ k, f k = ⋃ e ∈ E, e := by
      have h_finite_union : ∃ f : Fin E.card → Set Ω, (∀ k, f k ∈ E) ∧ (∀ k₁ k₂, k₁ ≠ k₂ → Disjoint (f k₁) (f k₂)) ∧ ∀ e ∈ E, ∃ k, f k = e := by
        have h_finite_union : Nonempty (Fin E.card ≃ E) := by
          exact ⟨ Fintype.equivOfCardEq <| by simp +decide ⟩;
        obtain ⟨ f ⟩ := h_finite_union;
        use fun k => f k |>.1;
        exact ⟨ fun k => f k |>.2, fun k₁ k₂ hk => hE₂ _ ( f k₁ |>.2 ) _ ( f k₂ |>.2 ) ( by simpa [ Fin.ext_iff ] using fun h => hk <| f.injective <| Subtype.ext h ), fun e he => ⟨ f.symm ⟨ e, he ⟩, by simp +decide ⟩ ⟩;
      obtain ⟨ f, hf₁, hf₂, hf₃ ⟩ := h_finite_union;
      refine' ⟨ f, hf₁, hf₂, _ ⟩;
      ext x; simp;
      exact ⟨ fun ⟨ k, hk ⟩ => ⟨ f k, hf₁ k, hk ⟩, fun ⟨ e, he, hx ⟩ => by obtain ⟨ k, rfl ⟩ := hf₃ e he; exact ⟨ k, hx ⟩ ⟩;
    use fun k => if hk : k < E.card then f ⟨k, hk⟩ else ∅;
    refine' ⟨ _, _, _ ⟩;
    · grind;
    · intro k₁ k₂ hk; by_cases hk₁ : k₁ < E.card <;> by_cases hk₂ : k₂ < E.card <;> simp +decide [ hk₁, hk₂ ] ;
      exact hf.2.1 _ _ ( by simpa [ Fin.ext_iff ] using hk );
    · simp +decide [ ← hf.2.2, Set.ext_iff ];
      exact fun x => ⟨ fun ⟨ i, hi ⟩ => by split_ifs at hi <;> [ exact ⟨ _, hi ⟩ ; exact False.elim ( absurd hi ( by simp +decide ) ) ], fun ⟨ i, hi ⟩ => ⟨ i, by simpa using hi ⟩ ⟩;
  refine' ⟨ f, _, _, hf.2.1, _ ⟩;
  · intro k; specialize hf; replace hf := hf.1 k; aesop;
  · intro k hk;
    cases' Finset.mem_union.mp ( hf.1 k ) with hk₁ hk₂ <;> simp_all +decide;
  · grind

/-- Basin coverage theorem when the infimum of invariant set measures is positive. -/
theorem exists_small_set_large_basin_of_pos_infimum
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {δ : ENNReal} (hδ : 0 < δ)
    (α : ENNReal) (hα : 0 < α)
    (hα_bound : ∀ E : Set Ω, MeasurableSet E → E =ᵐ[μ] T ⁻¹' E →
      0 < μ E → α ≤ μ E) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A ≤ δ ∧ μ (basin T A)ᶜ ≤ δ := by
  obtain ⟨E, hE_meas, hE_erg, hE_disj, hE_cover⟩ :=
    exists_ergodic_covering_of_pos_infimum μ T hT hap α hα hα_bound
  exact exists_small_set_large_basin_of_covering μ T hT hap hδ E hE_meas hE_erg hE_disj hE_cover

end Submission.ErgodicDecomp

end
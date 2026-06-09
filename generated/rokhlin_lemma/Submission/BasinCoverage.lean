import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.MarkerLemmas
import Submission.RokhlinCore

/-! ## Basin coverage infrastructure -/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Submission.RokhlinCore Submission.MarkerLemmas Submission.Helpers
open Classical

noncomputable section

namespace Submission.BasinCoverage

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Monotonicity -/

theorem basin_mono {T : Ω → Ω} {A B : Set Ω} (h : A ⊆ B) :
    basin T A ⊆ basin T B := by
  intro x hx
  simp only [basin, mem_iUnion, mem_preimage] at hx ⊢
  obtain ⟨k, hk⟩ := hx; exact ⟨k, h hk⟩

/-! ### Union -/

theorem basin_union {T : Ω → Ω} {A B : Set Ω} :
    basin T (A ∪ B) = basin T A ∪ basin T B := by
  ext x; simp only [basin, mem_iUnion, mem_preimage, mem_union]
  constructor
  · rintro ⟨k, hk | hk⟩ <;> [exact Or.inl ⟨k, hk⟩; exact Or.inr ⟨k, hk⟩]
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩) <;> [exact ⟨k, Or.inl hk⟩; exact ⟨k, Or.inr hk⟩]

theorem basin_iUnion {ι : Type*} {T : Ω → Ω} {A : ι → Set Ω} :
    basin T (⋃ i, A i) = ⋃ i, basin T (A i) := by
  ext x; simp only [basin, mem_iUnion, mem_preimage]
  constructor
  · rintro ⟨k, i, hi⟩; exact ⟨i, k, hi⟩
  · rintro ⟨i, k, hi⟩; exact ⟨k, i, hi⟩

/-! ### Forward invariance of basin complement -/

theorem basin_compl_subset_preimage {T : Ω → Ω} {A : Set Ω} :
    (basin T A)ᶜ ⊆ T ⁻¹' (basin T A)ᶜ := by
  intro x hx hTx
  apply hx
  simp only [basin, mem_iUnion, mem_preimage] at hTx ⊢
  obtain ⟨k, hk⟩ := hTx
  exact ⟨k + 1, by rwa [iterate_succ_apply]⟩

theorem basin_compl_forward_invariant {T : Ω → Ω} {A : Set Ω}
    {x : Ω} (hx : x ∈ (basin T A)ᶜ) : T x ∈ (basin T A)ᶜ :=
  basin_compl_subset_preimage hx

/-! ### a.e. invariance of basin complement -/

theorem basin_compl_ae_eq_preimage (μ : Measure Ω) [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    (basin T A)ᶜ =ᵐ[μ] T ⁻¹' (basin T A)ᶜ :=
  ae_eq_of_ae_subset_of_measure_ge
    (ae_of_all μ basin_compl_subset_preimage)
    (le_of_eq (hT.measure_preimage (basin_measurableSet hT.measurable hA).compl.nullMeasurableSet))
    (basin_measurableSet hT.measurable hA).compl.nullMeasurableSet
    (ne_of_lt (measure_lt_top μ _))

theorem measure_preimage_basin_compl_diff_eq_zero (μ : Measure Ω) {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A)
    [IsFiniteMeasure μ] :
    μ (T ⁻¹' (basin T A)ᶜ \ (basin T A)ᶜ) = 0 := by
  rw [measure_diff basin_compl_subset_preimage
      (basin_measurableSet hT.measurable hA).compl.nullMeasurableSet
      (ne_of_lt (measure_lt_top μ _)),
    hT.measure_preimage (basin_measurableSet hT.measurable hA).compl.nullMeasurableSet,
    tsub_self]

/-! ### Basin complement of union -/

theorem basin_compl_union {T : Ω → Ω} {A B : Set Ω} :
    (basin T (A ∪ B))ᶜ = (basin T A)ᶜ ∩ (basin T B)ᶜ := by
  rw [basin_union]; exact compl_union _ _

theorem basin_compl_union_subset {T : Ω → Ω} {A B : Set Ω} :
    (basin T (A ∪ B))ᶜ ⊆ (basin T A)ᶜ := by
  rw [basin_compl_union]; exact Set.inter_subset_left

/-! ### Basin complement is disjoint from marker -/

theorem basin_compl_disjoint_marker {T : Ω → Ω} {A : Set Ω} :
    Disjoint (basin T A)ᶜ A :=
  Set.disjoint_left.mpr fun x hx hxA => hx (basin_superset hxA)

/-! ### Measure of basin \ A -/

theorem measure_basin_diff_eq (μ : Measure Ω) {T : Ω → Ω}
    {A : Set Ω} (hA : MeasurableSet A)
    (hT : Measurable T) [IsFiniteMeasure μ] :
    μ (basin T A \ A) = μ (basin T A) - μ A :=
  measure_diff basin_superset hA.nullMeasurableSet (ne_of_lt (measure_lt_top μ _))

/-! ### Key invariance lemma for the identity argument -/

theorem ae_eq_id_of_all_subsets_ae_invariant
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    {C : Set Ω} (hC : MeasurableSet C) (hCinv : C =ᵐ[μ] T ⁻¹' C)
    (h_all : ∀ S : Set Ω, MeasurableSet S →
      μ (symmDiff (S ∩ C) (T ⁻¹' (S ∩ C))) = 0) :
    ∀ᵐ x ∂μ, x ∈ C → T x = x := by
  obtain ⟨G, hG_countable, hG_separating⟩ : ∃ (G : ℕ → Set Ω), (∀ i, MeasurableSet (G i)) ∧ (∀ x y : Ω, x ≠ y → ∃ i, x ∈ G i ∧ y ∉ G i ∨ x ∉ G i ∧ y ∈ G i) := by
    have h_countably_separated : MeasurableSpace.CountablySeparated Ω := by
      exact MeasurableSpace.countablySeparated_of_hasCountableSeparatingOn
    generalize_proofs at *; (
    rcases h_countably_separated with ⟨ G, hG_countable, hG_separating ⟩
    generalize_proofs at *; (
    have := hG_countable.exists_eq_range
    generalize_proofs at *; (
    by_cases hG_empty : G = ∅ <;> simp +decide [ hG_empty ] at hG_separating ⊢
    generalize_proofs at *; (
    exact ⟨ fun _ => ∅, fun _ => MeasurableSet.empty, fun x y hxy => False.elim <| hxy <| hG_separating x y ⟩);
    obtain ⟨ f, rfl ⟩ := this ( Set.nonempty_iff_ne_empty.mpr hG_empty ) ; exact ⟨ f, fun i => hG_separating.1 _ ( Set.mem_range_self _ ), fun x y hxy => by contrapose! hxy; exact hG_separating.2 x y fun s hs => by obtain ⟨ i, rfl ⟩ := hs; specialize hxy i; tauto ⟩ ;)))
  generalize_proofs at *; (
  have h_full_measure : ∀ i, ∀ᵐ x ∂μ, x ∈ C → (x ∈ G i ↔ T x ∈ G i) := by
    intro i
    have h_full_measure_i : μ (symmDiff (G i ∩ C) (T ⁻¹' (G i ∩ C))) = 0 := by
      exact h_all _ ( hG_countable i )
    generalize_proofs at *; (
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_full_measure_i, hCinv ] with x hx₁ hx₂ hx₃; simp_all +decide [ symmDiff ] ;
    tauto)
  generalize_proofs at *; (
  filter_upwards [ MeasureTheory.ae_all_iff.2 h_full_measure ] with x hx hx' using Classical.not_not.1 fun hx'' => by obtain ⟨ i, hi ⟩ := hG_separating _ _ hx''; specialize hx i; aesop;))

/-! ### Non-invariant subset existence -/

theorem exists_non_invariant_subset
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {C : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < μ C)
    (hCinv : C =ᵐ[μ] T ⁻¹' C) :
    ∃ S : Set Ω, MeasurableSet S ∧
      0 < μ (symmDiff (S ∩ C) (T ⁻¹' (S ∩ C))) := by
  contrapose! hCpos;
  have h_fixed_points : ∀ᵐ x ∂μ, x ∈ C → T x = x := by
    apply_rules [ ae_eq_id_of_all_subsets_ae_invariant ];
    exact fun S hS => le_antisymm ( hCpos S hS ) ( zero_le _ );
  have h_fixed_points : μ (C ∩ {x | T x = x}) = μ C := by
    rw [ MeasureTheory.measure_congr ];
    rw [ MeasureTheory.ae_eq_set ];
    simp_all +decide [ Set.diff_eq_empty.mpr ];
    exact MeasureTheory.measure_mono_null ( fun x hx => by aesop ) h_fixed_points;
  refine' h_fixed_points ▸ hap ▸ MeasureTheory.measure_mono _;
  exact fun x hx => ⟨ 1, zero_lt_one, by simpa using hx.2 ⟩

/-! ### Marker a.e. invariant when basin doesn't amplify -/

/-
If A ⊆ C (both measurable), C is a.e. T-invariant, and μ(basin T A ∩ C) ≤ μ(A),
    then A is a.e. T-invariant within C. Key steps:
    1. A ⊆ basin T A ∩ C and equal measure ⟹ basin T A ∩ C =ᵃᵉ A
    2. (basin T A)ᶜ ∩ C =ᵃᵉ Aᶜ ∩ C
    3. (basin T A)ᶜ ∩ C is a.e. T-invariant (intersection of invariants)
    4. Aᶜ ∩ C is a.e. T-invariant
    5. A ∩ C = C \ (Aᶜ ∩ C) is a.e. T-invariant
-/
theorem marker_ae_invariant_of_basin_le
    (μ : Measure Ω) [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ)
    {A C : Set Ω} (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hAC : A ⊆ C)
    (hCinv : C =ᵐ[μ] T ⁻¹' C)
    (hle : μ (basin T A ∩ C) ≤ μ A) :
    μ (symmDiff (A ∩ C) (T ⁻¹' (A ∩ C))) = 0 := by
  -- From steps 2 and 3: Aᶜ ∩ C =ᵐ[μ] T⁻¹'((basin T A)ᶜ ∩ C) =ᵐ[μ] T⁻¹'(Aᶜ ∩ C) (using step 2 again via MeasurePreserving).
  have h_symm : μ (symmDiff (Aᶜ ∩ C) (T⁻¹' (Aᶜ ∩ C))) = 0 := by
    have h_symm : μ (symmDiff ((basin T A)ᶜ ∩ C) (T⁻¹' ((basin T A)ᶜ ∩ C))) = 0 := by
      convert MeasureTheory.measure_symmDiff_eq_zero_iff ( μ := μ ) |>.1 _ using 1;
      rw [ MeasureTheory.measure_symmDiff_eq_zero_iff ];
      rw [ MeasureTheory.measure_symmDiff_eq_zero_iff ];
      convert MeasureTheory.ae_eq_set_inter ( basin_compl_ae_eq_preimage μ hT hA ) hCinv using 1;
    have h_symm : μ (symmDiff ((basin T A)ᶜ ∩ C) (Aᶜ ∩ C)) = 0 := by
      have h_symm : μ ((basin T A ∩ C) \ A) = 0 := by
        have h_symm : μ ((basin T A ∩ C) \ A) = μ (basin T A ∩ C) - μ A := by
          rw [ MeasureTheory.measure_diff ];
          · exact fun x hx => ⟨ basin_superset hx, hAC hx ⟩;
          · exact hA.nullMeasurableSet;
          · exact MeasureTheory.measure_ne_top _ _;
        rw [ h_symm, tsub_eq_zero_iff_le.mpr hle ];
      convert h_symm using 2 ; ext x ; by_cases hx : x ∈ A <;> simp +decide [ hx, symmDiff ];
      · exact fun h => False.elim <| h <| basin_superset hx;
      · tauto;
    have h_symm : μ (symmDiff (T⁻¹' ((basin T A)ᶜ ∩ C)) (T⁻¹' (Aᶜ ∩ C))) = 0 := by
      have h_symm : μ (T ⁻¹' (symmDiff ((basin T A)ᶜ ∩ C) (Aᶜ ∩ C))) = 0 := by
        rw [ hT.measure_preimage ] ; aesop ( simp_config := { singlePass := true } ) ;
        exact MeasureTheory.NullMeasurableSet.of_null h_symm;
      convert h_symm using 1;
    have h_symm : μ (symmDiff ((basin T A)ᶜ ∩ C) (T⁻¹' (Aᶜ ∩ C))) = 0 := by
      refine' MeasureTheory.measure_mono_null _ ( MeasureTheory.measure_union_null ‹μ ( symmDiff ( ( basin T A ) ᶜ ∩ C ) ( T ⁻¹' ( ( basin T A ) ᶜ ∩ C ) ) ) = 0› ‹μ ( symmDiff ( T ⁻¹' ( ( basin T A ) ᶜ ∩ C ) ) ( T ⁻¹' ( A ᶜ ∩ C ) ) ) = 0› );
      grind +qlia;
    have h_symm : μ (symmDiff (Aᶜ ∩ C) ((basin T A)ᶜ ∩ C)) = 0 := by
      rw [ symmDiff_comm ] ; assumption;
    have h_symm : μ (symmDiff (Aᶜ ∩ C) (T⁻¹' (Aᶜ ∩ C))) ≤ μ (symmDiff (Aᶜ ∩ C) ((basin T A)ᶜ ∩ C)) + μ (symmDiff ((basin T A)ᶜ ∩ C) (T⁻¹' (Aᶜ ∩ C))) := by
      refine' le_trans ( MeasureTheory.measure_mono _ ) ( MeasureTheory.measure_union_le _ _ );
      grind +extAll;
    exact le_antisymm ( h_symm.trans ( by aesop ) ) ( zero_le _ );
  convert h_symm using 1;
  convert MeasureTheory.measure_congr _ using 2;
  · infer_instance;
  · rw [ MeasureTheory.ae_eq_set ] at *;
    constructor <;> refine' MeasureTheory.measure_mono_null _ _;
    any_goals exact C \ T ⁻¹' C ∪ T ⁻¹' C \ C;
    · grind;
    · exact MeasureTheory.measure_union_null hCinv.1 hCinv.2;
    · grind +qlia;
    · exact MeasureTheory.measure_union_null hCinv.1 hCinv.2

/-- If A ⊆ C where C is a.e. T-invariant, and A is not a.e. T-invariant within C,
    then the basin of A covers strictly more than A within C. -/
theorem basin_covers_more_than_marker
    (μ : Measure Ω) [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ)
    {A C : Set Ω} (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hAC : A ⊆ C)
    (hCinv : C =ᵐ[μ] T ⁻¹' C)
    (hA_noninv : 0 < μ (symmDiff (A ∩ C) (T ⁻¹' (A ∩ C)))) :
    μ A < μ (basin T A ∩ C) := by
  by_contra h
  push_neg at h
  exact absurd (marker_ae_invariant_of_basin_le μ hT hA hC hAC hCinv h)
    (ne_of_gt hA_noninv)

/-! ### Ergodic restricted sweep-out lemma -/

/-
On an ergodic component C, any positive-measure marker A ⊆ C has basin covering C a.e.
    The key observation: (basin T A)ᶜ ∩ C is a.e. T-invariant (intersection of two
    a.e. invariant sets) and disjoint from A. By the ergodicity hypothesis on C,
    it is either null or conull in C. If conull, then μ(A) = 0, contradicting hApos.
    So it must be null, i.e., μ(C \ basin T A) = 0.
-/
theorem ergodic_on_basin_full
    (μ : Measure Ω) [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ)
    {C : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < μ C)
    (hCinv : C =ᵐ[μ] T ⁻¹' C)
    (herg : ∀ D : Set Ω, MeasurableSet D → D ⊆ C →
      D =ᵐ[μ] T ⁻¹' D → μ D = 0 ∨ μ (C \ D) = 0)
    {A : Set Ω} (hA : MeasurableSet A) (hAC : A ⊆ C)
    (hApos : 0 < μ A) :
    μ (C \ basin T A) = 0 := by
  contrapose! herg;
  refine' ⟨ ( basin T A ) ᶜ ∩ C, _, _, _, _, _ ⟩;
  · exact MeasurableSet.inter ( MeasurableSet.compl ( basin_measurableSet ( hT.measurable ) hA ) ) hC;
  · exact Set.inter_subset_right;
  · convert MeasureTheory.ae_eq_set_inter ( basin_compl_ae_eq_preimage μ hT hA ) hCinv using 1;
  · convert herg using 1;
    exact congr_arg _ ( by ext; simp +decide [ and_comm ] );
  · refine' ne_of_gt ( lt_of_lt_of_le hApos ( MeasureTheory.measure_mono _ ) );
    exact fun x hx => ⟨ hAC hx, fun hx' => hx'.1 <| basin_superset hx ⟩

/-
Invariant-set splitting: if C is a positive-measure a.e. invariant set that is
    not ergodic in the restricted sense, then there exists a measurable a.e. invariant
    subset D ⊆ C with both D and C \ D having positive measure.
-/
theorem exists_invariant_split
    (μ : Measure Ω) [IsFiniteMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ)
    {C : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < μ C)
    (hCinv : C =ᵐ[μ] T ⁻¹' C)
    (hnoterg : ¬ (∀ D : Set Ω, MeasurableSet D → D ⊆ C →
      D =ᵐ[μ] T ⁻¹' D → μ D = 0 ∨ μ (C \ D) = 0)) :
    ∃ D : Set Ω, MeasurableSet D ∧ D ⊆ C ∧
      D =ᵐ[μ] T ⁻¹' D ∧ 0 < μ D ∧ 0 < μ (C \ D) := by
  contrapose! hnoterg;
  exact fun D hD hDC hDinv => Classical.or_iff_not_imp_left.2 fun h => le_antisymm ( hnoterg D hD hDC hDinv ( lt_of_le_of_ne ( zero_le _ ) ( Ne.symm h ) ) ) ( zero_le _ )

/-! ### Small subset within a positive-measure set -/

/-
In a non-atomic standard Borel space, any positive-measure measurable set
    has a measurable subset of positive measure at most δ.
-/
theorem exists_small_measurableSet_subset
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] [NoAtoms μ]
    {C : Set Ω} (hC : MeasurableSet C) (hCpos : 0 < μ C)
    {δ : ENNReal} (hδ : 0 < δ) :
    ∃ A : Set Ω, MeasurableSet A ∧ A ⊆ C ∧ 0 < μ A ∧ μ A ≤ δ := by
  by_contra h_contra;
  -- By repeatedly applying the splitting lemma, we can find a measurable subset $A \subseteq C$ such that $0 < \mu(A) \leq \delta$.
  have h_induction : ∀ n : ℕ, ∃ A : Set Ω, MeasurableSet A ∧ A ⊆ C ∧ μ A ≤ (1 / 2 : ENNReal) ^ n * μ C ∧ 0 < μ A := by
    intro n
    induction' n with n ih
    generalize_proofs at *; (
    exact ⟨ C, hC, Set.Subset.refl _, by simp +decide, hCpos ⟩);
    obtain ⟨ A, hA₁, hA₂, hA₃, hA₄ ⟩ := ih
    have h_split : ∃ B : Set Ω, MeasurableSet B ∧ B ⊆ A ∧ μ B ≤ (1 / 2 : ENNReal) * μ A ∧ 0 < μ B := by
      obtain ⟨ B, hB₁, hB₂, hB₃ ⟩ := Submission.SmallSets.exists_measurableSet_of_lt_measure μ hA₁ hA₄
      generalize_proofs at *; (
      by_cases hB₄ : μ B ≤ (1 / 2 : ENNReal) * μ A;
      · exact ⟨ B, hB₁, hB₂, hB₄, hB₃.1 ⟩;
      · use A \ B, by
          exact hA₁.diff hB₁, by
          grind, by
          rw [ MeasureTheory.measure_diff ] <;> norm_num [ hA₁, hB₁, hB₂ ];
          rw [ ← ENNReal.toReal_le_toReal ] at * <;> norm_num at *;
          · rw [ ENNReal.toReal_add ] <;> norm_num at * ; linarith [ ENNReal.toReal_pos hA₄.ne' ( MeasureTheory.measure_ne_top _ _ ) ] ;
            exact ENNReal.mul_ne_top ( by norm_num ) ( MeasureTheory.measure_ne_top _ _ );
          · exact ENNReal.mul_ne_top ( by simp +decide ) ( by simp +decide );
          · exact ENNReal.mul_ne_top ( by norm_num ) ( MeasureTheory.measure_ne_top _ _ );
          · exact ENNReal.mul_ne_top ( by norm_num ) ( MeasureTheory.measure_ne_top _ _ ), by
          rw [ MeasureTheory.measure_diff ] <;> norm_num [ hA₁, hB₁, hB₂ ];
          exact hB₃.2)
    generalize_proofs at *; (
    obtain ⟨ B, hB₁, hB₂, hB₃, hB₄ ⟩ := h_split; use B; simp_all +decide [ pow_succ', mul_assoc ] ;
    exact ⟨ hB₂.trans hA₂, hB₃.trans ( mul_le_mul_left' hA₃ _ ) ⟩);
  -- Choose $n$ such that $(1 / 2)^n * \mu C < \delta$.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ENNReal) ^ n * μ C < δ := by
    have h_lim : Filter.Tendsto (fun n : ℕ => (1 / 2 : ENNReal) ^ n * μ C) Filter.atTop (nhds 0) := by
      convert ENNReal.Tendsto.mul_const ( ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one _ ) _ <;> norm_num;
    exact ( h_lim.eventually ( gt_mem_nhds hδ ) ) |> fun h => h.exists;
  exact h_contra <| by obtain ⟨ A, hA₁, hA₂, hA₃, hA₄ ⟩ := h_induction n; exact ⟨ A, hA₁, hA₂, hA₄, hA₃.trans hn.le ⟩ ;

/-! ### Ergodic case of basin coverage -/

/-
For ergodic T, any δ > 0 admits a marker of measure ≤ δ whose basin covers Ω a.e.
-/
theorem exists_small_set_large_basin_ergodic
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    (herg : ∀ D : Set Ω, MeasurableSet D →
      D =ᵐ[μ] T ⁻¹' D → μ D = 0 ∨ μ Dᶜ = 0)
    {δ : ENNReal} (hδ : 0 < δ) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A ≤ δ ∧ μ (basin T A)ᶜ = 0 := by
  obtain ⟨A, hA_meas, hA_pos, hA_le⟩ : ∃ A : Set Ω, MeasurableSet A ∧ 0 < μ A ∧ μ A ≤ δ := by
    have h_no_atoms : NoAtoms μ := Submission.NoAtoms.noAtoms_of_aperiodic μ T hT hap
    exact Submission.SmallSets.exists_small_measurableSet μ hδ;
  refine' ⟨ A, hA_meas, hA_le, _ ⟩;
  contrapose! herg;
  refine' ⟨ ( basin T A ) ᶜ, _, _, _, _ ⟩;
  · apply_rules [ MeasurableSet.compl, basin_measurableSet ];
    exact hT.measurable;
  · apply_rules [ basin_compl_ae_eq_preimage ];
  · exact herg;
  · simp only [compl_compl]
    exact ne_of_gt ( lt_of_lt_of_le hA_pos ( MeasureTheory.measure_mono basin_superset ) )

/-! ### A.e. invariance of countable intersections -/

/-
Countable intersection of a.e. invariant sets is a.e. invariant.
-/
theorem ae_invariant_iInter
    (μ : Measure Ω) {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ)
    {C : ℕ → Set Ω} (hC_meas : ∀ k, MeasurableSet (C k))
    (hCinv : ∀ k, C k =ᵐ[μ] T ⁻¹' (C k)) :
    (⋂ k, C k) =ᵐ[μ] T ⁻¹' (⋂ k, C k) := by
  simp +decide only [preimage_iInter]
  exact EventuallyEq.countable_iInter hCinv

/- NOTE: exists_small_set_large_basin has been moved to GeneralBasin.lean as
   exists_small_set_large_basin_v2, which handles the positive-infimum case (proved)
   and the zero-infimum case (sorry). The main proof in Submission.lean now uses v2.
   Removing the sorry here to prevent circular proof discovery by `exact?`/`grind`. -/

end Submission.BasinCoverage

end
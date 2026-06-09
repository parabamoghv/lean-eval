import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.OrbitLemmas

/-! ## Marker / base-set lemmas toward the Rokhlin tower

### Key construction: `longReturnSet`

Given a measurable set `A` and height `n`, define
  `longReturnSet T A n = A ∩ ⋂ k ∈ Finset.range (n-1), (T^[k+1])⁻¹' Aᶜ`

### Warnings (non-invertibility)

- `T` is only assumed `MeasurePreserving`, NOT injective.
- Forward images `T^[k] '' B` may not be measurable.
- Floors 1,…,n-1 among themselves are NOT guaranteed pairwise disjoint
  by `longReturnSet` alone.
-/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Classical

namespace Submission.MarkerLemmas

/-! ### The `longReturnSet` construction -/

/-- The set of points in `A` whose next `n - 1` forward iterates all avoid `A`. -/
noncomputable def longReturnSet {Ω : Type*} (T : Ω → Ω) (A : Set Ω) (n : ℕ) : Set Ω :=
  A ∩ ⋂ k ∈ Finset.range (n - 1), (T^[k + 1])⁻¹' Aᶜ

theorem longReturnSet_subset {Ω : Type*} (T : Ω → Ω) (A : Set Ω) (n : ℕ) :
    longReturnSet T A n ⊆ A :=
  inter_subset_left

theorem mem_longReturnSet_iff {Ω : Type*} {T : Ω → Ω} {A : Set Ω} {n : ℕ} {x : Ω} :
    x ∈ longReturnSet T A n ↔ x ∈ A ∧ ∀ k, k < n - 1 → T^[k + 1] x ∉ A := by
  simp only [longReturnSet, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range,
    Set.mem_preimage, Set.mem_compl_iff]

theorem longReturnSet_iterate_not_mem {Ω : Type*} {T : Ω → Ω} {A : Set Ω} {n : ℕ}
    {x : Ω} (hx : x ∈ longReturnSet T A n) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k ≤ n - 1) : T^[k] x ∉ A := by
  rw [mem_longReturnSet_iff] at hx
  have hk' : k - 1 < n - 1 := by omega
  have := hx.2 (k - 1) hk'
  rwa [Nat.sub_add_cancel hk1] at this

theorem longReturnSet_measurableSet {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {A : Set Ω} {n : ℕ}
    (hT : Measurable T) (hA : MeasurableSet A) :
    MeasurableSet (longReturnSet T A n) := by
  unfold longReturnSet
  apply MeasurableSet.inter hA
  apply MeasurableSet.biInter (Finset.range (n - 1)).countable_toSet
  intro k _
  exact (hT.iterate (k + 1)) hA.compl

/-! ### Partial tower disjointness -/

/-- Forward image of `longReturnSet` under `T^[k]` avoids `A` for `1 ≤ k ≤ n-1`. -/
theorem towerFloor_longReturnSet_subset_compl {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {A : Set Ω}
    {n : ℕ} {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    towerFloor T (longReturnSet T A n) k ⊆ Aᶜ := by
  intro y hy
  rw [Helpers.mem_towerFloor_iff] at hy
  obtain ⟨b, hb, rfl⟩ := hy
  exact longReturnSet_iterate_not_mem hb hk1 hk2

/-- Floor 0 is disjoint from floor `k` for `1 ≤ k ≤ n - 1`. -/
theorem disjoint_floor_zero_of_longReturnSet {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {A : Set Ω}
    {n : ℕ} {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    Disjoint (towerFloor T (longReturnSet T A n) 0)
             (towerFloor T (longReturnSet T A n) k) := by
  rw [Helpers.towerFloor_zero]
  exact Set.disjoint_of_subset_left (longReturnSet_subset T A n)
    (Set.disjoint_of_subset_right (towerFloor_longReturnSet_subset_compl hk1 hk2)
      disjoint_compl_right)

/-! ### First-entry layers (skyscraper decomposition) -/

/-- Points that first enter `A` at exactly step `k`. -/
noncomputable def firstEntryLayer {Ω : Type*} (T : Ω → Ω) (A : Set Ω) (k : ℕ) : Set Ω :=
  (T^[k] ⁻¹' A) \ ⋃ j ∈ Finset.range k, (T^[j] ⁻¹' A)

theorem firstEntryLayer_measurableSet {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {A : Set Ω} {k : ℕ}
    (hT : Measurable T) (hA : MeasurableSet A) :
    MeasurableSet (firstEntryLayer T A k) := by
  apply MeasurableSet.diff
  · exact (hT.iterate k) hA
  · apply MeasurableSet.biUnion (Finset.range k).countable_toSet
    intro j _
    exact (hT.iterate j) hA

theorem firstEntryLayer_pairwiseDisjoint {Ω : Type*} (T : Ω → Ω) (A : Set Ω) :
    Pairwise (Disjoint on firstEntryLayer T A) := by
  intro i j hij
  simp only [Function.onFun, firstEntryLayer]
  rw [Set.disjoint_left]
  intro x ⟨hxi, hxi'⟩ ⟨hxj, hxj'⟩
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_preimage, not_exists] at hxi' hxj'
  rcases lt_or_gt_of_ne hij with h | h
  · exact (hxj' i h) hxi
  · exact (hxi' j h) hxj

theorem firstEntryLayer_zero {Ω : Type*} (T : Ω → Ω) (A : Set Ω) :
    firstEntryLayer T A 0 = A := by
  simp [firstEntryLayer]

/-- The basin of `A` equals `⋃_k firstEntryLayer T A k = ⋃_k (T^[k])⁻¹' A`. -/
theorem iUnion_firstEntryLayer_eq {Ω : Type*} (T : Ω → Ω) (A : Set Ω) :
    ⋃ k, firstEntryLayer T A k = ⋃ k, (T^[k] ⁻¹' A) := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, hk.1⟩
  · rintro ⟨k, hk⟩
    have hex : ∃ m, x ∈ T^[m] ⁻¹' A := ⟨k, hk⟩
    refine ⟨Nat.find hex, ?_⟩
    constructor
    · exact Nat.find_spec hex
    · simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_preimage, not_exists]
      intro j hj; exact Nat.find_min hex hj

theorem firstEntryLayer_subset_preimage {Ω : Type*} (T : Ω → Ω) (A : Set Ω) (k : ℕ) :
    firstEntryLayer T A k ⊆ T^[k] ⁻¹' A :=
  diff_subset

/-! ### Conservative dynamics -/

theorem conservative_of_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Conservative T μ :=
  hT.conservative

theorem ae_frequently_return {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω)
    (hcons : Conservative T μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ, x ∈ A → ∃ᶠ k in Filter.atTop, T^[k] x ∈ A :=
  hcons.ae_mem_imp_frequently_image_mem hA.nullMeasurableSet

theorem ae_return_to_set {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω)
    (hcons : Conservative T μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂μ, x ∈ A → ∃ k, 0 < k ∧ T^[k] x ∈ A := by
  filter_upwards [ae_frequently_return μ T hcons hA] with x hx hxA
  have hfreq := hx hxA
  rw [Filter.Frequently] at hfreq
  by_contra h_none
  push_neg at h_none
  apply hfreq
  rw [Filter.eventually_atTop]
  exact ⟨1, fun k hk => h_none k hk⟩

/-! ### Measure estimates -/

theorem measure_preimage_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) (k : ℕ) :
    μ ((T^[k]) ⁻¹' A) = μ A :=
  (hT.iterate k).measure_preimage hA.nullMeasurableSet

theorem measure_firstEntryLayer_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) (k : ℕ) :
    μ (firstEntryLayer T A k) ≤ μ A := by
  calc μ (firstEntryLayer T A k)
      ≤ μ (T^[k] ⁻¹' A) := measure_mono (firstEntryLayer_subset_preimage T A k)
    _ = μ A := measure_preimage_eq μ T hT hA k

/-
The total measure of entry layers at depths 1 through m is at most `m * μ(A)`.
-/
theorem measure_firstEntryLayers_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A)
    (m : ℕ) :
    μ (⋃ k ∈ Finset.range m, firstEntryLayer T A (k + 1)) ≤ m * μ A := by
  refine' le_trans ( MeasureTheory.measure_biUnion_finset_le _ _ ) _;
  exact le_trans ( Finset.sum_le_sum fun _ _ => measure_firstEntryLayer_le μ T hT hA _ ) ( by simp +decide )

/-
The early-return subset of A has measure ≤ `(n-1) * μ(A)`.
-/
theorem measure_early_return_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A)
    (n : ℕ) :
    μ (A ∩ ⋃ k ∈ Finset.range (n - 1), (T^[k + 1])⁻¹' A)
      ≤ (n - 1) * μ A := by
  refine' le_trans ( MeasureTheory.measure_mono ( Set.inter_subset_right ) ) _;
  refine' le_trans ( MeasureTheory.measure_biUnion_finset_le _ _ ) _;
  rw [ Finset.sum_congr rfl fun _ _ => measure_preimage_eq _ _ hT hA _ ] ; cases n <;> aesop

/-
Lower bound for `longReturnSet`: `μ(longReturnSet T A n) ≥ μ(A) - earlyReturn`.
-/
theorem measure_longReturnSet_ge {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {T : Ω → Ω}
    {A : Set Ω} (_hA : MeasurableSet A)
    {n : ℕ} :
    μ A - μ (A ∩ ⋃ k ∈ Finset.range (n - 1), (T^[k + 1])⁻¹' A)
      ≤ μ (longReturnSet T A n) := by
  refine' tsub_le_iff_left.mpr _;
  refine' le_trans _ ( MeasureTheory.measure_union_le _ _ );
  refine' MeasureTheory.measure_mono _;
  intro x hx; by_cases h : ∃ k < n - 1, T^[k + 1] x ∈ A <;> simp_all +decide [ longReturnSet ] ;

end Submission.MarkerLemmas
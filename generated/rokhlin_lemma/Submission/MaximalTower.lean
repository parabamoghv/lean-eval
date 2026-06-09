import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.OrbitLemmas
import Submission.MarkerLemmas

/-! ## Kakutani tower base and floor disjointness

### Key construction

Given a measurable "marker" set `A` and height `n`, define
  `kakutaniBase T A n = ⋃ m, firstEntryLayer T A ((m + 1) * n)`

This collects all points whose first entry time to `A` is a positive
multiple of `n`.

### Main result

`isRokhlinTower_kakutaniBase`: The forward-image floors
  `T^[0] '' B, T^[1] '' B, ..., T^[n-1] '' B`
are pairwise disjoint.

**Proof idea:** For `x ∈ firstEntryLayer T A M` and `i ≤ M`, we have
`T^[i](x) ∈ firstEntryLayer T A (M - i)`. So forward-image floors
land in levels with indices `{(m+1)n - i : m ≥ 0}`. For `i ≠ j`
(both `< n`), these index sets are disjoint (mod `n` argument), and
`firstEntryLayer`s with different indices are pairwise disjoint.

### Warnings
- `T` is only `MeasurePreserving`, NOT injective.
- Forward images `T^[k] '' B` may not be measurable.
- The disjointness here is GENUINE set-theoretic disjointness
  of forward images, even for non-invertible `T`.
-/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Submission.MarkerLemmas Submission.Helpers
open Classical

namespace Submission.MaximalTower

/-! ### Definition of `kakutaniBase` -/

/-- The Kakutani tower base: points whose first entry time to `A` is a
positive multiple of `n`. -/
noncomputable def kakutaniBase {Ω : Type*} (T : Ω → Ω) (A : Set Ω) (n : ℕ) : Set Ω :=
  ⋃ m : ℕ, firstEntryLayer T A ((m + 1) * n)

theorem kakutaniBase_def {Ω : Type*} (T : Ω → Ω) (A : Set Ω) (n : ℕ) :
    kakutaniBase T A n = ⋃ m : ℕ, firstEntryLayer T A ((m + 1) * n) := rfl

theorem mem_kakutaniBase_iff {Ω : Type*} {T : Ω → Ω} {A : Set Ω} {n : ℕ} {x : Ω} :
    x ∈ kakutaniBase T A n ↔ ∃ m : ℕ, x ∈ firstEntryLayer T A ((m + 1) * n) := by
  simp [kakutaniBase]

/-! ### Measurability -/

theorem kakutaniBase_measurableSet {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {A : Set Ω} {n : ℕ}
    (hT : Measurable T) (hA : MeasurableSet A) :
    MeasurableSet (kakutaniBase T A n) := by
  apply MeasurableSet.iUnion
  intro m
  exact firstEntryLayer_measurableSet hT hA

/-! ### The key floor-shifting lemma -/

/-- For `x ∈ firstEntryLayer T A M` and `i ≤ M`,
`T^[i](x) ∈ firstEntryLayer T A (M - i)`.

This is the structural heart of the disjointness proof: iterating `T`
decrements the first-entry index by exactly `i`. -/
theorem iterate_mem_firstEntryLayer_sub {Ω : Type*}
    {T : Ω → Ω} {A : Set Ω}
    {M i : ℕ} (hi : i ≤ M) {x : Ω} (hx : x ∈ firstEntryLayer T A M) :
    T^[i] x ∈ firstEntryLayer T A (M - i) := by
  simp only [firstEntryLayer, mem_diff, mem_preimage,
    mem_iUnion, Finset.mem_range] at hx ⊢
  refine ⟨?_, ?_⟩
  · rw [← iterate_add_apply, Nat.sub_add_cancel hi]; exact hx.1
  · intro ⟨j, hj, hjA⟩
    have hjA' : T^[j + i] x ∈ A := by rw [iterate_add_apply]; exact hjA
    exact hx.2 ⟨j + i, by omega, hjA'⟩

/-- Forward image of `firstEntryLayer T A M` under `T^[i]` is contained
in `firstEntryLayer T A (M - i)` when `i ≤ M`. -/
theorem image_iterate_firstEntryLayer_subset {Ω : Type*}
    {T : Ω → Ω} {A : Set Ω}
    {M i : ℕ} (hi : i ≤ M) :
    T^[i] '' (firstEntryLayer T A M) ⊆ firstEntryLayer T A (M - i) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  exact iterate_mem_firstEntryLayer_sub hi hx

/-! ### Floor disjointness for `kakutaniBase` -/

/-- **Main theorem:** The forward-image floors of `kakutaniBase T A n`
are pairwise disjoint, giving a valid Rokhlin tower of height `n`.

The proof works even for non-invertible `T` because the disjointness
follows from the level structure of `firstEntryLayer`, not from
injectivity of `T`. -/
theorem isRokhlinTower_kakutaniBase {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {A : Set Ω} {n : ℕ}
    (hT : Measurable T) (hA : MeasurableSet A) (_hn : 0 < n) :
    IsRokhlinTower T (kakutaniBase T A n) n := by
  refine ⟨kakutaniBase_measurableSet hT hA, ?_⟩
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  rw [mem_towerFloor_iff] at hz₁ hz₂
  obtain ⟨b₁, hb₁, rfl⟩ := hz₁
  obtain ⟨b₂, hb₂, hb₂_eq⟩ := hz₂
  simp only [kakutaniBase, Set.mem_iUnion] at hb₁ hb₂
  obtain ⟨m₁, hm₁⟩ := hb₁
  obtain ⟨m₂, hm₂⟩ := hb₂
  have hi_le : i ≤ (m₁ + 1) * n := by nlinarith
  have hj_le : j ≤ (m₂ + 1) * n := by nlinarith
  -- T^[i] b₁ is in firstEntryLayer at index (m₁+1)*n - i
  have hb₁' : T^[i] b₁ ∈ firstEntryLayer T A ((m₁ + 1) * n - i) :=
    iterate_mem_firstEntryLayer_sub hi_le hm₁
  -- T^[i] b₁ = T^[j] b₂ is also in firstEntryLayer at index (m₂+1)*n - j
  have hb₂' : T^[i] b₁ ∈ firstEntryLayer T A ((m₂ + 1) * n - j) := by
    rw [← hb₂_eq]; exact iterate_mem_firstEntryLayer_sub hj_le hm₂
  -- The two indices must differ (mod n argument)
  have h_ne : (m₁ + 1) * n - i ≠ (m₂ + 1) * n - j := by
    intro heq
    zify [hi_le, hj_le] at heq
    have key : ((m₁ : ℤ) - m₂) * n = (i : ℤ) - j := by linarith
    rcases eq_or_ne m₁ m₂ with rfl | hne
    · simp at key; exact hij (by omega)
    · rcases Nat.lt_or_gt_of_ne hne with h1 | h1
      · have : ((m₂ : ℤ) - m₁) * n ≥ n := by
          nlinarith [show (m₂ : ℤ) - m₁ ≥ 1 from by omega]
        linarith
      · have : ((m₁ : ℤ) - m₂) * n ≥ n := by
          nlinarith [show (m₁ : ℤ) - m₂ ≥ 1 from by omega]
        linarith
  -- firstEntryLayers at different indices are pairwise disjoint
  exact Set.disjoint_left.mp (firstEntryLayer_pairwiseDisjoint T A h_ne) hb₁' hb₂'

/-! ### Structural properties -/

/-- The `kakutaniBase` is disjoint from the marker set `A` when `n ≥ 1`.
Every element has first entry time ≥ `n ≥ 1`, so the element
itself is not in `A`. -/
theorem kakutaniBase_disjoint_marker {Ω : Type*}
    {T : Ω → Ω} {A : Set Ω} {n : ℕ}
    (_hn : 1 ≤ n) : Disjoint (kakutaniBase T A n) A := by
  rw [Set.disjoint_left]
  intro x hx hxA
  simp only [kakutaniBase, Set.mem_iUnion] at hx
  obtain ⟨m, hm⟩ := hx
  simp only [firstEntryLayer, mem_diff, mem_preimage,
    mem_iUnion, Finset.mem_range] at hm
  exact hm.2 ⟨0, by positivity, by simpa using hxA⟩

/-- The `kakutaniBase` is a subset of the basin of `A`. -/
theorem kakutaniBase_subset_basin {Ω : Type*}
    {T : Ω → Ω} {A : Set Ω} {n : ℕ} :
    kakutaniBase T A n ⊆ ⋃ k : ℕ, T^[k] ⁻¹' A := by
  intro x hx
  rw [mem_kakutaniBase_iff] at hx
  obtain ⟨m, hm⟩ := hx
  rw [mem_iUnion]
  exact ⟨(m + 1) * n, (firstEntryLayer_subset_preimage T A _) hm⟩

/-- Each floor of the tower based on `kakutaniBase` is contained in a
union of `firstEntryLayer`s at congruent indices. -/
theorem towerFloor_kakutaniBase_subset {Ω : Type*}
    {T : Ω → Ω} {A : Set Ω}
    {n i : ℕ} (hi : i < n) :
    towerFloor T (kakutaniBase T A n) i ⊆
      ⋃ m : ℕ, firstEntryLayer T A ((m + 1) * n - i) := by
  intro z hz
  rw [mem_towerFloor_iff] at hz
  obtain ⟨b, hb, rfl⟩ := hz
  simp only [kakutaniBase, Set.mem_iUnion] at hb
  obtain ⟨m, hm⟩ := hb
  rw [mem_iUnion]
  exact ⟨m, iterate_mem_firstEntryLayer_sub (by nlinarith) hm⟩

/-! ### Monotonicity and Zorn infrastructure -/

/-- Rokhlin tower property is monotone downward: subsets of tower bases
are also tower bases. -/
theorem isRokhlinTower_subset {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {B C : Set Ω} {n : ℕ}
    (hC : IsRokhlinTower T C n) (hBC : B ⊆ C) (hB : MeasurableSet B) :
    IsRokhlinTower T B n := by
  refine ⟨hB, ?_⟩
  intro i hi j hj hij
  exact Disjoint.mono (Set.image_mono hBC) (Set.image_mono hBC)
    (hC.2 hi hj hij)

/-- Union of a chain of Rokhlin tower bases is a Rokhlin tower base
(assuming measurability of the union). -/
theorem isRokhlinTower_iUnion_chain {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {n : ℕ} {ι : Type*}
    {B : ι → Set Ω}
    (hB : ∀ i, IsRokhlinTower T (B i) n)
    (hchain : IsChain (· ⊆ ·) (Set.range B))
    (hmeas : MeasurableSet (⋃ i, B i)) :
    IsRokhlinTower T (⋃ i, B i) n := by
  refine ⟨hmeas, ?_⟩
  intro k hk l hl hkl
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  rw [towerFloor_def, Set.mem_image] at hz₁ hz₂
  obtain ⟨b₁, hb₁, rfl⟩ := hz₁
  obtain ⟨b₂, hb₂, hb₂_eq⟩ := hz₂
  rw [Set.mem_iUnion] at hb₁ hb₂
  obtain ⟨i₁, hi₁⟩ := hb₁
  obtain ⟨i₂, hi₂⟩ := hb₂
  suffices ∃ i, b₁ ∈ B i ∧ b₂ ∈ B i from by
    obtain ⟨i, h1, h2⟩ := this
    exact Set.disjoint_left.mp ((hB i).2 hk hl hkl)
      (Set.mem_image_of_mem _ h1) (by rw [← hb₂_eq]; exact Set.mem_image_of_mem _ h2)
  by_cases heq : B i₁ = B i₂
  · exact ⟨i₁, hi₁, heq ▸ hi₂⟩
  · rcases hchain (Set.mem_range_self i₁) (Set.mem_range_self i₂) heq with h12 | h21
    · exact ⟨i₂, h12 hi₁, hi₂⟩
    · exact ⟨i₁, hi₁, h21 hi₂⟩

end Submission.MaximalTower

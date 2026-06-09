import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MarkerLemmas
import Submission.MaximalTower

/-! ## Shadow sets and inter-tower disjointness

### Goal

Given an existing Rokhlin tower base `B` and a new marker set `A`, we want to
show that `B ∪ kakutaniBase T A n` is again a valid Rokhlin tower base,
provided `A` is "far enough" from `B` in the orbit sense.

### Key definition: `forwardBasin`

`forwardBasin T A = ⋃ k, (T^[k+1])⁻¹' A` — points with some positive
iterate in `A`. This is measurable (countable union of preimages of a
measurable set).

### Main result

If `Disjoint B (forwardBasin T A)` (no positive iterate of any `b ∈ B` lands
in `A`), then the floors of `B` and `kakutaniBase T A n` are cross-disjoint,
so `B ∪ kakutaniBase T A n` is a valid Rokhlin tower.

### Non-invertibility

The disjointness argument works for non-invertible `T`. It uses the
`firstEntryLayer` level structure, not injectivity.
-/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Submission.Helpers Submission.MarkerLemmas Submission.MaximalTower
open Classical

namespace Submission.Shadow

/-! ### Forward basin -/

/-- Points with some positive iterate in `A`. -/
def forwardBasin {Ω : Type*} (T : Ω → Ω) (A : Set Ω) : Set Ω :=
  ⋃ k : ℕ, (T^[k + 1])⁻¹' A

theorem mem_forwardBasin_iff {Ω : Type*} {T : Ω → Ω} {A : Set Ω} {x : Ω} :
    x ∈ forwardBasin T A ↔ ∃ k : ℕ, T^[k + 1] x ∈ A := by
  simp [forwardBasin]

theorem forwardBasin_measurableSet {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {A : Set Ω}
    (hT : Measurable T) (hA : MeasurableSet A) :
    MeasurableSet (forwardBasin T A) := by
  apply MeasurableSet.iUnion
  intro k
  exact (hT.iterate (k + 1)) hA

/-- `forwardBasin T A` is monotone in `A`. -/
theorem forwardBasin_mono {Ω : Type*} {T : Ω → Ω} {A₁ A₂ : Set Ω} (h : A₁ ⊆ A₂) :
    forwardBasin T A₁ ⊆ forwardBasin T A₂ := by
  intro x hx
  rw [mem_forwardBasin_iff] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, h hk⟩

/-! ### Union of two Rokhlin towers -/

/-- The tower floor of a union is the union of tower floors. -/
theorem towerFloor_union {Ω : Type*} (T : Ω → Ω) (B C : Set Ω) (k : ℕ) :
    towerFloor T (B ∪ C) k = towerFloor T B k ∪ towerFloor T C k := by
  simp [towerFloor_def, Set.image_union]

/-- Union of two Rokhlin tower bases is a Rokhlin tower base, given
    cross-disjointness of all floor pairs. -/
theorem isRokhlinTower_union {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {B C : Set Ω} {n : ℕ}
    (hB : IsRokhlinTower T B n) (hC : IsRokhlinTower T C n)
    (hcross : ∀ i, i < n → ∀ j, j < n →
              Disjoint (towerFloor T B i) (towerFloor T C j))
    (hmeas : MeasurableSet (B ∪ C)) :
    IsRokhlinTower T (B ∪ C) n := by
  refine ⟨hmeas, ?_⟩
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  simp only [Function.onFun, towerFloor_union]
  exact Disjoint.union_left
    (Disjoint.union_right (hB.2 (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hij)
      (hcross i hi j hj))
    (Disjoint.union_right ((hcross j hj i hi).symm)
      (hC.2 (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hij))

/-! ### Cross-disjointness from forward basin avoidance -/

/-- **Key lemma:** If `b ∈ B`, `c ∈ kakutaniBase T A n`, and
    `T^[i] b = T^[j] c` for some `i, j < n`, then some positive
    iterate of `b` lands in `A`.

    This is the structural heart of the inter-tower disjointness argument. -/
theorem exists_positive_iterate_in_marker {Ω : Type*}
    {T : Ω → Ω} {A : Set Ω} {n : ℕ} (_hn : 0 < n)
    {b c : Ω} (hc : c ∈ kakutaniBase T A n)
    {i j : ℕ} (_hi : i < n) (hj : j < n)
    (heq : T^[i] b = T^[j] c) :
    ∃ K : ℕ, 0 < K ∧ T^[K] b ∈ A := by
  rw [mem_kakutaniBase_iff] at hc
  obtain ⟨m, hm⟩ := hc
  -- c ∈ firstEntryLayer T A ((m+1)*n), so T^[(m+1)*n] c ∈ A
  have hc_entry : T^[(m + 1) * n] c ∈ A :=
    (firstEntryLayer_subset_preimage T A _) hm
  have hj_le : j ≤ (m + 1) * n := by nlinarith
  -- T^[(m+1)*n - j] (T^[j] c) = T^[(m+1)*n] c ∈ A
  have step : T^[(m + 1) * n - j] (T^[j] c) ∈ A := by
    rw [← iterate_add_apply, Nat.sub_add_cancel hj_le]
    exact hc_entry
  -- Since T^[i] b = T^[j] c, we get T^[(m+1)*n - j + i] b ∈ A
  set K := (m + 1) * n - j + i
  have step2 : T^[K] b ∈ A := by
    have h1 : T^[(m + 1) * n - j] (T^[i] b) ∈ A := by rw [heq]; exact step
    rw [← iterate_add_apply] at h1
    exact h1
  -- The exponent is positive
  have hK_pos : 0 < K := by
    have : (m + 1) * n ≥ n := Nat.le_mul_of_pos_left n (by omega)
    omega
  exact ⟨K, hK_pos, step2⟩

/-- If `B` avoids the forward basin of `A`, then floors of `B` are
    disjoint from floors of `kakutaniBase T A n`. -/
theorem cross_disjoint_of_disjoint_forwardBasin {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {A B : Set Ω} {n : ℕ} (hn : 0 < n)
    (hdisj : Disjoint B (forwardBasin T A))
    {i j : ℕ} (hi : i < n) (hj : j < n) :
    Disjoint (towerFloor T B i) (towerFloor T (kakutaniBase T A n) j) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  rw [mem_towerFloor_iff] at hz1 hz2
  obtain ⟨b, hbB, rfl⟩ := hz1
  obtain ⟨c, hcK, hcz⟩ := hz2
  -- From the overlap, some positive iterate of b lands in A
  obtain ⟨K, hK_pos, hK_mem⟩ :=
    exists_positive_iterate_in_marker hn hcK hi hj hcz.symm
  -- But b ∈ B and B avoids forwardBasin T A
  have : b ∈ forwardBasin T A := by
    rw [mem_forwardBasin_iff]
    exact ⟨K - 1, by rwa [Nat.sub_one_add_one_eq_of_pos hK_pos]⟩
  exact Set.disjoint_left.mp hdisj hbB this

/-! ### The main extension lemma -/

/-- **Extension lemma:** If `B` is a Rokhlin tower base and `A` is a
    measurable marker set whose forward basin avoids `B`, then
    `B ∪ kakutaniBase T A n` is also a Rokhlin tower base.

    This is the key ingredient for the exhaustion/Zorn argument. -/
theorem isRokhlinTower_union_kakutaniBase {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {A B : Set Ω} {n : ℕ} (hn : 0 < n)
    (hT : Measurable T) (hA : MeasurableSet A)
    (hB_tower : IsRokhlinTower T B n)
    (hdisj : Disjoint B (forwardBasin T A)) :
    IsRokhlinTower T (B ∪ kakutaniBase T A n) n := by
  apply isRokhlinTower_union hB_tower (isRokhlinTower_kakutaniBase hT hA hn)
  · intro i hi j hj
    exact cross_disjoint_of_disjoint_forwardBasin hn hdisj hi hj
  · exact hB_tower.1.union (kakutaniBase_measurableSet hT hA)

/-- Disjointness of `B` and `kakutaniBase T A n` follows from the
    forward basin condition. -/
theorem disjoint_base_kakutaniBase_of_forwardBasin {Ω : Type*}
    {T : Ω → Ω} {A B : Set Ω} {n : ℕ} (hn : 1 ≤ n)
    (hdisj : Disjoint B (forwardBasin T A)) :
    Disjoint B (kakutaniBase T A n) := by
  rw [Set.disjoint_left]
  intro b hbB hbK
  rw [mem_kakutaniBase_iff] at hbK
  obtain ⟨m, hm⟩ := hbK
  have := (firstEntryLayer_subset_preimage T A _) hm
  have hK_pos : 0 < (m + 1) * n := by positivity
  have : b ∈ forwardBasin T A := by
    rw [mem_forwardBasin_iff]
    exact ⟨(m + 1) * n - 1, by rwa [Nat.sub_one_add_one_eq_of_pos hK_pos]⟩
  exact Set.disjoint_left.mp hdisj hbB this

/-! ### Tower union monotonicity under extension -/

/-- The tower union of `B ∪ C` contains the tower union of `B`. -/
theorem towerUnion_union_left {Ω : Type*} (T : Ω → Ω) (B C : Set Ω) (n : ℕ) :
    towerUnion T B n ⊆ towerUnion T (B ∪ C) n := by
  intro x hx
  rw [mem_towerUnion_iff] at hx ⊢
  obtain ⟨k, hk, hxk⟩ := hx
  refine ⟨k, hk, ?_⟩
  rw [towerFloor_union]
  exact Set.mem_union_left _ hxk

/-- The tower union of `B ∪ C` contains the tower union of `C`. -/
theorem towerUnion_union_right {Ω : Type*} (T : Ω → Ω) (B C : Set Ω) (n : ℕ) :
    towerUnion T C n ⊆ towerUnion T (B ∪ C) n := by
  intro x hx
  rw [mem_towerUnion_iff] at hx ⊢
  obtain ⟨k, hk, hxk⟩ := hx
  refine ⟨k, hk, ?_⟩
  rw [towerFloor_union]
  exact Set.mem_union_right _ hxk


/-! ### Tower union disjointness -/

/-- If two towers have cross-disjoint floors, their tower unions are disjoint. -/
theorem disjoint_towerUnion_of_cross_disjoint {Ω : Type*}
    {T : Ω → Ω} {B C : Set Ω} {n : ℕ}
    (hcross : ∀ i, i < n → ∀ j, j < n →
              Disjoint (towerFloor T B i) (towerFloor T C j)) :
    Disjoint (towerUnion T B n) (towerUnion T C n) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  rw [mem_towerUnion_iff] at hx1 hx2
  obtain ⟨i, hi, hxi⟩ := hx1
  obtain ⟨j, hj, hxj⟩ := hx2
  exact Set.disjoint_left.mp (hcross i hi j hj) hxi hxj

/-- If `B` avoids `forwardBasin T A`, the existing and new tower unions are disjoint. -/
theorem disjoint_towerUnion_kakutaniBase {Ω : Type*} [MeasurableSpace Ω]
    {T : Ω → Ω} {A B : Set Ω} {n : ℕ} (hn : 0 < n)
    (hdisj : Disjoint B (forwardBasin T A)) :
    Disjoint (towerUnion T B n) (towerUnion T (kakutaniBase T A n) n) :=
  disjoint_towerUnion_of_cross_disjoint
    (fun _i hi _j hj => cross_disjoint_of_disjoint_forwardBasin hn hdisj hi hj)

/-! ### Tower union decomposition for the combined tower -/

/-- The tower union of `B ∪ C` equals the union of their individual tower unions
    (set equality, not just inclusion). -/
theorem towerUnion_union_eq {Ω : Type*}
    (T : Ω → Ω) (B C : Set Ω) (n : ℕ) :
    towerUnion T (B ∪ C) n = towerUnion T B n ∪ towerUnion T C n := by
  ext x
  simp only [mem_towerUnion_iff, towerFloor_union, Set.mem_union]
  constructor
  · rintro ⟨k, hk, hxk | hxk⟩
    · exact Or.inl ⟨k, hk, hxk⟩
    · exact Or.inr ⟨k, hk, hxk⟩
  · rintro (⟨k, hk, hxk⟩ | ⟨k, hk, hxk⟩)
    · exact ⟨k, hk, Or.inl hxk⟩
    · exact ⟨k, hk, Or.inr hxk⟩

end Submission.Shadow

import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.OrbitLemmas
import Submission.MarkerLemmas
import Submission.MaximalTower
import Submission.RokhlinCore

/-! ## Generalized residue-class Kakutani tower

### Key construction: `kakutaniBaseR`

Given a measurable "marker" set `A`, height `n ≥ 1`, and residue `r < n`,
define

  `kakutaniBaseR T A n r = ⋃ m, firstEntryLayer T A (r + (m + 1) * n)`

This collects points whose first entry time to `A` is congruent to `r`
modulo `n` and at least `r + n` (hence ≥ n > i for all floor indices i < n).

When `r = 0`, this equals the original `kakutaniBase T A n`.

### Main results

- `isRokhlinTower_kakutaniBaseR`: valid Rokhlin tower of height `n`.
- `measure_towerUnion_kakutaniBaseR_ge`: `n * μ(base) ≤ μ(towerUnion)`.
- `exists_good_residue_tower`: pigeonhole gives a tower with measure ≥ late layers.
- `exists_tower_from_basin`: best tower has measure ≥ μ(basin\A) - (n-1)*μ(A).
-/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Submission.MarkerLemmas Submission.Helpers Submission.MaximalTower
open Submission.RokhlinCore
open Classical

noncomputable section

namespace Submission.ResidueTower

set_option linter.unusedVariables false

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Definition -/

/-- The generalized Kakutani tower base at residue `r`:
points whose first entry time to `A` is ≡ `r` (mod `n`) and ≥ `r + n`. -/
def kakutaniBaseR {Ω : Type*} (T : Ω → Ω) (A : Set Ω) (n : ℕ) (r : ℕ) : Set Ω :=
  ⋃ m : ℕ, firstEntryLayer T A (r + (m + 1) * n)

/-! ### Basic properties -/

omit [MeasurableSpace Ω] in
theorem mem_kakutaniBaseR_iff {T : Ω → Ω} {A : Set Ω} {n r : ℕ} {x : Ω} :
    x ∈ kakutaniBaseR T A n r ↔ ∃ m : ℕ, x ∈ firstEntryLayer T A (r + (m + 1) * n) := by
  simp [kakutaniBaseR]

theorem kakutaniBaseR_zero_eq {Ω : Type*} {T : Ω → Ω} {A : Set Ω} {n : ℕ} :
    kakutaniBaseR T A n 0 = kakutaniBase T A n := by
  simp [kakutaniBaseR, kakutaniBase]

theorem kakutaniBaseR_measurableSet {T : Ω → Ω} {A : Set Ω} {n r : ℕ}
    (hT : Measurable T) (hA : MeasurableSet A) :
    MeasurableSet (kakutaniBaseR T A n r) := by
  apply MeasurableSet.iUnion
  intro m
  exact firstEntryLayer_measurableSet hT hA

/-! ### Floor-shifting for kakutaniBaseR -/

omit [MeasurableSpace Ω] in
theorem towerFloor_kakutaniBaseR_subset_shifted {T : Ω → Ω} {A : Set Ω}
    {n r i : ℕ} (hi : i < n) :
    towerFloor T (kakutaniBaseR T A n r) i ⊆
      ⋃ m : ℕ, firstEntryLayer T A (r + (m + 1) * n - i) := by
  intro z hz
  rw [mem_towerFloor_iff] at hz
  obtain ⟨b, hb, rfl⟩ := hz
  rw [mem_kakutaniBaseR_iff] at hb
  obtain ⟨m, hm⟩ := hb
  rw [mem_iUnion]
  exact ⟨m, iterate_mem_firstEntryLayer_sub (by nlinarith) hm⟩

/-! ### Measurable separators for kakutaniBaseR floors -/

def levelSetR (T : Ω → Ω) (A : Set Ω) (n r i : ℕ) : Set Ω :=
  ⋃ m : ℕ, firstEntryLayer T A (r + (m + 1) * n - i)

theorem levelSetR_measurableSet {T : Ω → Ω} {A : Set Ω} {n r i : ℕ}
    (hT : Measurable T) (hA : MeasurableSet A) :
    MeasurableSet (levelSetR T A n r i) := by
  apply MeasurableSet.iUnion; intro m
  exact firstEntryLayer_measurableSet hT hA

omit [MeasurableSpace Ω] in
theorem towerFloor_kakutaniBaseR_subset_levelSetR
    {T : Ω → Ω} {A : Set Ω} {n r i : ℕ} (hi : i < n) :
    towerFloor T (kakutaniBaseR T A n r) i ⊆ levelSetR T A n r i :=
  towerFloor_kakutaniBaseR_subset_shifted hi

omit [MeasurableSpace Ω] in
theorem disjoint_levelSetR {T : Ω → Ω} {A : Set Ω} {n r : ℕ} (_hn : 0 < n)
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    Disjoint (levelSetR T A n r i) (levelSetR T A n r j) := by
  apply Set.disjoint_iUnion_left.mpr
  intro m₁; apply Set.disjoint_iUnion_right.mpr; intro m₂
  refine firstEntryLayer_pairwiseDisjoint _ _ ?_
  intro h
  have hle₁ : i ≤ r + (m₁ + 1) * n := by nlinarith
  have hle₂ : j ≤ r + (m₂ + 1) * n := by nlinarith
  zify [hle₁, hle₂] at h
  have key : ((m₁ : ℤ) - m₂) * n = (i : ℤ) - j := by linarith
  rcases eq_or_ne m₁ m₂ with rfl | hne
  · simp at key; exact hij (by omega)
  · rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · nlinarith [show (m₂ : ℤ) - m₁ ≥ 1 from by omega]
    · nlinarith [show (m₁ : ℤ) - m₂ ≥ 1 from by omega]

/-! ### Tower disjointness -/

theorem isRokhlinTower_kakutaniBaseR {T : Ω → Ω} {A : Set Ω} {n r : ℕ}
    (hT : Measurable T) (hA : MeasurableSet A) (hn : 0 < n) :
    IsRokhlinTower T (kakutaniBaseR T A n r) n := by
  refine ⟨kakutaniBaseR_measurableSet hT hA, ?_⟩
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  rw [mem_towerFloor_iff] at hz₁ hz₂
  obtain ⟨b₁, hb₁, rfl⟩ := hz₁
  obtain ⟨b₂, hb₂, hb₂_eq⟩ := hz₂
  rw [mem_kakutaniBaseR_iff] at hb₁ hb₂
  obtain ⟨m₁, hm₁⟩ := hb₁
  obtain ⟨m₂, hm₂⟩ := hb₂
  have hi_le : i ≤ r + (m₁ + 1) * n := by nlinarith
  have hj_le : j ≤ r + (m₂ + 1) * n := by nlinarith
  have hb₁' := iterate_mem_firstEntryLayer_sub hi_le hm₁
  have hb₂' : T^[i] b₁ ∈ firstEntryLayer T A (r + (m₂ + 1) * n - j) := by
    rw [← hb₂_eq]; exact iterate_mem_firstEntryLayer_sub hj_le hm₂
  have h_ne : r + (m₁ + 1) * n - i ≠ r + (m₂ + 1) * n - j := by
    intro heq
    zify [hi_le, hj_le] at heq
    have key : ((m₁ : ℤ) - m₂) * n = (i : ℤ) - j := by linarith
    rcases eq_or_ne m₁ m₂ with rfl | hne
    · simp at key; exact hij (by omega)
    · rcases Nat.lt_or_gt_of_ne hne with h1 | h1
      · nlinarith [show (m₂ : ℤ) - m₁ ≥ 1 from by omega]
      · nlinarith [show (m₁ : ℤ) - m₂ ≥ 1 from by omega]
  exact Set.disjoint_left.mp (firstEntryLayer_pairwiseDisjoint T A h_ne) hb₁' hb₂'

/-! ### Tower measure bound -/

theorem measure_towerUnion_kakutaniBaseR_ge
    (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A)
    {n : ℕ} (hn : 0 < n) (r : ℕ) :
    n * μ (kakutaniBaseR T A n r) ≤ μ (towerUnion T (kakutaniBaseR T A n r) n) := by
  have h_sum_le_union :
      (∑ i ∈ Finset.range n, μ (towerFloor T (kakutaniBaseR T A n r) i)) ≤
        μ (towerUnion T (kakutaniBaseR T A n r) n) := by
    convert sum_measure_le_of_separated μ
      (fun i : Fin n => towerFloor T (kakutaniBaseR T A n r) i)
      (fun i : Fin n => levelSetR T A n r i) ?_ ?_ ?_ using 1
    · rw [Finset.sum_range]
    · congr; ext; simp [towerUnion]
      exact ⟨fun ⟨i, hi, hi'⟩ => ⟨⟨i, hi⟩, hi'⟩, fun ⟨i, hi'⟩ => ⟨i, i.2, hi'⟩⟩
    · exact fun i => levelSetR_measurableSet hT.measurable hA
    · intro i _ j _ hij
      exact disjoint_levelSetR hn (Fin.is_lt i) (Fin.is_lt j) (by simpa [Fin.ext_iff] using hij)
    · exact fun i => towerFloor_kakutaniBaseR_subset_levelSetR (Fin.is_lt i)
  have h_floor_ge_base :
      ∀ i ∈ Finset.range n,
        μ (towerFloor T (kakutaniBaseR T A n r) i) ≥ μ (kakutaniBaseR T A n r) := by
    intro i _
    apply measure_image_iterate_ge μ T hT (kakutaniBaseR_measurableSet hT.measurable hA) i
  exact le_trans (by simpa using Finset.sum_le_sum h_floor_ge_base) h_sum_le_union

/-! ### Disjointness across residue classes -/

theorem disjoint_kakutaniBaseR {Ω : Type*} {T : Ω → Ω} {A : Set Ω} {n : ℕ}
    {r₁ r₂ : ℕ} (hr₁ : r₁ < n) (hr₂ : r₂ < n) (hne : r₁ ≠ r₂) :
    Disjoint (kakutaniBaseR T A n r₁) (kakutaniBaseR T A n r₂) := by
  apply Set.disjoint_iUnion_left.mpr
  intro m₁; apply Set.disjoint_iUnion_right.mpr; intro m₂
  refine firstEntryLayer_pairwiseDisjoint _ _ ?_
  intro h; apply hne
  have h1 : (r₁ + (m₁ + 1) * n) % n = r₁ := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hr₁
  have h2 : (r₂ + (m₂ + 1) * n) % n = r₂ := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hr₂
  rw [h] at h1; linarith

theorem iUnion_kakutaniBaseR_eq {Ω : Type*} {T : Ω → Ω} {A : Set Ω} {n : ℕ}
    (hn : 0 < n) :
    ⋃ r ∈ Finset.range n, kakutaniBaseR T A n r =
      ⋃ (k : ℕ) (_ : k ≥ n), firstEntryLayer T A k := by
  ext x
  constructor
  · intro hx
    simp only [mem_iUnion, Finset.mem_range, kakutaniBaseR] at hx
    obtain ⟨r, hr, m, hm⟩ := hx
    simp only [mem_iUnion, ge_iff_le]
    exact ⟨r + (m + 1) * n, by nlinarith, hm⟩
  · intro hx
    simp only [mem_iUnion, ge_iff_le] at hx
    obtain ⟨k, hk, hxk⟩ := hx
    simp only [mem_iUnion, Finset.mem_range, kakutaniBaseR]
    refine ⟨k % n, Nat.mod_lt k hn, k / n - 1, ?_⟩
    convert hxk using 2
    have h1 : 1 ≤ k / n := Nat.div_pos hk hn
    rw [Nat.sub_add_cancel h1, add_comm]
    have := Nat.div_add_mod k n
    linarith

/-! ### Subset of basin \ A -/

theorem kakutaniBaseR_subset_basin_diff {Ω : Type*}
    {T : Ω → Ω} {A : Set Ω} {n r : ℕ} (hn : 0 < n) :
    kakutaniBaseR T A n r ⊆ basin T A \ A := by
  intro x hx
  simp only [kakutaniBaseR, mem_iUnion] at hx
  obtain ⟨m, hm⟩ := hx
  constructor
  · rw [basin_eq_iUnion_firstEntryLayer]
    exact mem_iUnion.mpr ⟨_, hm⟩
  · intro hxA
    simp only [firstEntryLayer, mem_diff, mem_preimage, mem_iUnion,
      Finset.mem_range, not_exists] at hm
    exact hm.2 0 (by nlinarith [Nat.succ_pos m]) hxA

/-! ### Sum of measures across residue classes -/

theorem sum_measure_kakutaniBaseR_eq_biUnion (μ : Measure Ω)
    {T : Ω → Ω} {A : Set Ω} {n : ℕ} (hn : 0 < n)
    (hT : Measurable T) (hA : MeasurableSet A) :
    ∑ r ∈ Finset.range n, μ (kakutaniBaseR T A n r) =
      μ (⋃ r ∈ Finset.range n, kakutaniBaseR T A n r) := by
  rw [measure_biUnion_finset]
  · intro r₁ hr₁ r₂ hr₂ hne
    exact disjoint_kakutaniBaseR (Finset.mem_range.mp hr₁)
      (Finset.mem_range.mp hr₂) hne
  · intro r _
    exact kakutaniBaseR_measurableSet hT hA

theorem sum_measure_kakutaniBaseR_eq (μ : Measure Ω)
    {T : Ω → Ω} {A : Set Ω} {n : ℕ} (hn : 0 < n)
    (hT : Measurable T) (hA : MeasurableSet A) :
    ∑ r ∈ Finset.range n, μ (kakutaniBaseR T A n r) =
      μ (⋃ (k : ℕ) (_ : k ≥ n), firstEntryLayer T A k) := by
  rw [sum_measure_kakutaniBaseR_eq_biUnion μ hn hT hA, iUnion_kakutaniBaseR_eq hn]

/-! ### Pigeonhole lemma -/

private theorem ennreal_pigeonhole {n : ℕ} (hn : 0 < n) (f : Fin n → ENNReal) :
    ∃ i : Fin n, ∑ j, f j ≤ n * f i := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, hi⟩ := Finite.exists_max f
  exact ⟨i, calc ∑ j, f j
      ≤ ∑ _ : Fin n, f i := Finset.sum_le_sum (fun j _ => hi j)
    _ = n * f i := by simp [Finset.sum_const]⟩

theorem exists_kakutaniBaseR_ge_avg (μ : Measure Ω)
    {T : Ω → Ω} {A : Set Ω} {n : ℕ} (hn : 0 < n)
    (hT : Measurable T) (hA : MeasurableSet A) :
    ∃ r, r < n ∧
      μ (⋃ (k : ℕ) (_ : k ≥ n), firstEntryLayer T A k) ≤
        n * μ (kakutaniBaseR T A n r) := by
  have h_sum := sum_measure_kakutaniBaseR_eq μ hn hT hA
  obtain ⟨⟨r, hr⟩, hrle⟩ := ennreal_pigeonhole hn
    (fun i : Fin n => μ (kakutaniBaseR T A n i))
  refine ⟨r, hr, ?_⟩
  rw [← h_sum]
  convert hrle using 1
  rw [Finset.sum_range]

/-! ### Combined: best residue class gives a good tower -/

theorem exists_good_residue_tower (μ : Measure Ω)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    {A : Set Ω} (hA : MeasurableSet A)
    {n : ℕ} (hn : 0 < n) :
    ∃ r, r < n ∧
      IsRokhlinTower T (kakutaniBaseR T A n r) n ∧
      μ (⋃ (k : ℕ) (_ : k ≥ n), firstEntryLayer T A k) ≤
        μ (towerUnion T (kakutaniBaseR T A n r) n) := by
  obtain ⟨r, hr, hge⟩ := exists_kakutaniBaseR_ge_avg μ hn hT.measurable hA
  exact ⟨r, hr, isRokhlinTower_kakutaniBaseR hT.measurable hA hn,
    le_trans hge (measure_towerUnion_kakutaniBaseR_ge μ T hT hA hn r)⟩

/-! ### Basin decomposition lemmas -/

theorem basin_diff_eq_iUnion_pos {Ω : Type*} (T : Ω → Ω) (A : Set Ω) :
    basin T A \ A = ⋃ (k : ℕ) (_ : 0 < k), firstEntryLayer T A k := by
  ext x
  simp only [mem_diff, mem_iUnion]
  constructor
  · rintro ⟨hb, hxA⟩
    rw [basin_eq_iUnion_firstEntryLayer] at hb
    obtain ⟨k, hk⟩ := mem_iUnion.mp hb
    rcases k with _ | k
    · simp [firstEntryLayer_zero] at hk; exact absurd hk hxA
    · exact ⟨k + 1, Nat.succ_pos _, hk⟩
  · rintro ⟨k, hk, hxk⟩
    constructor
    · rw [basin_eq_iUnion_firstEntryLayer]; exact mem_iUnion.mpr ⟨k, hxk⟩
    · intro hxA
      simp only [firstEntryLayer, mem_diff, mem_preimage, mem_iUnion,
        Finset.mem_range, not_exists] at hxk
      exact hxk.2 0 hk hxA

theorem basin_diff_partition {Ω : Type*} {T : Ω → Ω} {A : Set Ω} {n : ℕ} (hn : 0 < n) :
    basin T A \ A =
      (⋃ (k : ℕ) (_ : k ≥ n), firstEntryLayer T A k) ∪
      (⋃ (k : ℕ) (_ : 0 < k ∧ k < n), firstEntryLayer T A k) := by
  rw [basin_diff_eq_iUnion_pos]
  ext x; simp only [mem_iUnion, mem_union, ge_iff_le]
  constructor
  · rintro ⟨k, hk, hx⟩
    rcases Nat.lt_or_ge k n with h | h
    · exact Or.inr ⟨k, ⟨hk, h⟩, hx⟩
    · exact Or.inl ⟨k, h, hx⟩
  · rintro (⟨k, hk, hx⟩ | ⟨k, ⟨hk1, _⟩, hx⟩)
    · exact ⟨k, by omega, hx⟩
    · exact ⟨k, hk1, hx⟩

theorem disjoint_late_early {Ω : Type*} {T : Ω → Ω} {A : Set Ω} {n : ℕ} :
    Disjoint
      (⋃ (k : ℕ) (_ : k ≥ n), firstEntryLayer T A k)
      (⋃ (k : ℕ) (_ : 0 < k ∧ k < n), firstEntryLayer T A k) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  simp only [mem_iUnion, ge_iff_le] at hx₁ hx₂
  obtain ⟨k₁, hk₁, hxk₁⟩ := hx₁
  obtain ⟨k₂, ⟨_, hk₂b⟩, hxk₂⟩ := hx₂
  exact Set.disjoint_left.mp
    (firstEntryLayer_pairwiseDisjoint T A (show k₁ ≠ k₂ by omega)) hxk₁ hxk₂

theorem measure_late_plus_early {μ : Measure Ω}
    {T : Ω → Ω} (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A)
    {n : ℕ} (hn : 0 < n) :
    μ (⋃ (k : ℕ) (_ : k ≥ n), firstEntryLayer T A k) +
      μ (⋃ (k : ℕ) (_ : 0 < k ∧ k < n), firstEntryLayer T A k) =
    μ (basin T A \ A) := by
  rw [basin_diff_partition hn, measure_union disjoint_late_early]
  exact MeasurableSet.iUnion fun k =>
    MeasurableSet.iUnion fun _ => firstEntryLayer_measurableSet hT hA

theorem measure_early_layers_le (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A)
    {n : ℕ} :
    μ (⋃ (k : ℕ) (_ : 0 < k ∧ k < n), firstEntryLayer T A k) ≤ ↑(n - 1) * μ A := by
  have h_sub : (⋃ (k : ℕ) (_ : 0 < k ∧ k < n), firstEntryLayer T A k) ⊆
      ⋃ k ∈ Finset.range (n - 1), firstEntryLayer T A (k + 1) := by
    intro x hx
    simp only [mem_iUnion] at hx ⊢
    obtain ⟨k, ⟨hk1, hk2⟩, hxk⟩ := hx
    exact ⟨k - 1, by simp [Finset.mem_range]; omega, by rwa [Nat.sub_add_cancel hk1]⟩
  exact le_trans (measure_mono h_sub) (measure_firstEntryLayers_le μ T hT hA _)

/-! ### Main tower existence from basin -/

theorem exists_tower_from_basin (μ : Measure Ω)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    {A : Set Ω} (hA : MeasurableSet A)
    {n : ℕ} (hn : 0 < n) :
    ∃ B : Set Ω, IsRokhlinTower T B n ∧
      μ (basin T A \ A) - ↑(n - 1) * μ A ≤ μ (towerUnion T B n) := by
  obtain ⟨r, _, htower, hge⟩ := exists_good_residue_tower μ T hT hA hn
  refine ⟨kakutaniBaseR T A n r, htower, ?_⟩
  have h_decomp := measure_late_plus_early hT.measurable hA hn (μ := μ)
  have h_early := measure_early_layers_le μ T hT hA (n := n)
  calc μ (basin T A \ A) - ↑(n - 1) * μ A
      = μ (⋃ (k : ℕ) (_ : k ≥ n), firstEntryLayer T A k) +
        μ (⋃ (k : ℕ) (_ : 0 < k ∧ k < n), firstEntryLayer T A k) -
        ↑(n - 1) * μ A := by rw [h_decomp]
    _ ≤ μ (⋃ (k : ℕ) (_ : k ≥ n), firstEntryLayer T A k) := by
        rw [tsub_le_iff_left, add_comm (↑(n - 1) * μ A)]
        gcongr
    _ ≤ μ (towerUnion T (kakutaniBaseR T A n r) n) := hge

end Submission.ResidueTower

end

import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.OrbitLemmas
import Submission.MarkerLemmas
import Submission.MaximalTower

/-! ## Core Rokhlin lemma proof infrastructure -/

open LeanEval.Dynamics
open MeasureTheory Set Function
open Submission.Helpers Submission.MarkerLemmas Submission.MaximalTower
open Classical

noncomputable section

namespace Submission.RokhlinCore

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Carathéodory decomposition for separated sets -/

/-- If sets S_i are contained in pairwise disjoint measurable sets E_i,
    then μ(⋃ S_i) ≥ ∑ μ(S_i). -/
theorem sum_measure_le_of_separated
    {n : ℕ} (μ : Measure Ω) (S E : Fin n → Set Ω)
    (hE_meas : ∀ i, MeasurableSet (E i))
    (hE_disj : Set.PairwiseDisjoint Set.univ E)
    (hSE : ∀ i, S i ⊆ E i) :
    ∑ i : Fin n, μ (S i) ≤ μ (⋃ i, S i) := by
  induction' n with n ih <;> simp_all +decide [ Fin.sum_univ_castSucc, Finset.sum_range, Finset.mem_univ, MeasureTheory.measure_iUnion ];
  have h_inter : μ (⋃ i, S i) = μ ((⋃ i, S i) ∩ E (Fin.last n)) + μ ((⋃ i, S i) \ E (Fin.last n)) := by
    rw [ ← MeasureTheory.measure_inter_add_diff _ ( hE_meas ( Fin.last n ) ) ];
  have h_inter : μ ((⋃ i, S i) ∩ E (Fin.last n)) = μ (S (Fin.last n)) := by
    congr with x ; simp +decide [ hSE ];
    constructor <;> intro hx;
    · obtain ⟨ ⟨ i, hi ⟩, hx ⟩ := hx;
      have := hE_disj ( Set.mem_univ i ) ( Set.mem_univ ( Fin.last n ) ) ; simp_all +decide [ Set.disjoint_left ] ;
      grind;
    · exact ⟨ ⟨ _, hx ⟩, hSE _ hx ⟩;
  have h_inter : μ ((⋃ i, S i) \ E (Fin.last n)) ≥ μ (⋃ i : Fin n, S (Fin.castSucc i)) := by
    refine' MeasureTheory.measure_mono _;
    simp +decide [ Set.subset_def ];
    exact fun x i hi => ⟨ ⟨ _, hi ⟩, fun hx => by have := hE_disj ( Set.mem_univ ( Fin.castSucc i ) ) ( Set.mem_univ ( Fin.last n ) ) ( ne_of_lt ( Fin.castSucc_lt_last i ) ) ; exact this.le_bot ⟨ hSE _ hi, hx ⟩ ⟩;
  have := ih ( fun i => S ( Fin.castSucc i ) ) ( fun i => E ( Fin.castSucc i ) ) ( fun i => hE_meas _ ) ( fun i _ j _ hij => hE_disj ( Set.mem_univ _ ) ( Set.mem_univ _ ) ( by simpa [ Fin.ext_iff ] using hij ) ) ( fun i => hSE _ ) ; simp_all +decide [ Fin.sum_univ_castSucc ] ;
  rw [ add_comm ] ; gcongr;
  exact le_trans this h_inter

/-! ### Outer measure bound for forward images -/

/-- For measure-preserving T, μ(B) ≤ μ(T^[k] '' B). -/
theorem measure_image_iterate_ge (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {B : Set Ω} (hB : MeasurableSet B) (k : ℕ) :
    μ B ≤ μ (T^[k] '' B) := by
  obtain ⟨M, hM_meas, hM_sub, hM_eq⟩ := MeasureTheory.exists_measurable_superset μ (T^[k] '' B)
  have h_preimage : μ (T^[k] ⁻¹' M) = μ M := by
    convert measure_preimage_iterate hT k hM_sub using 1
  exact hM_eq ▸ h_preimage ▸ MeasureTheory.measure_mono
    (show B ⊆ T^[k] ⁻¹' M from fun x hx => hM_meas (Set.mem_image_of_mem _ hx))

/-! ### Measurable separators for tower floors -/

def levelSet (T : Ω → Ω) (A : Set Ω) (n i : ℕ) : Set Ω :=
  ⋃ m : ℕ, firstEntryLayer T A ((m + 1) * n - i)

theorem levelSet_measurableSet {T : Ω → Ω} {A : Set Ω} {n i : ℕ}
    (hT : Measurable T) (hA : MeasurableSet A) :
    MeasurableSet (levelSet T A n i) := by
  apply MeasurableSet.iUnion; intro m
  exact firstEntryLayer_measurableSet hT hA

theorem towerFloor_kakutaniBase_subset_levelSet
    {Ω : Type*} {T : Ω → Ω} {A : Set Ω} {n i : ℕ} (hi : i < n) :
    towerFloor T (kakutaniBase T A n) i ⊆ levelSet T A n i := by
  intro z hz
  rw [mem_towerFloor_iff] at hz
  obtain ⟨b, hb, rfl⟩ := hz
  simp only [kakutaniBase_def, Set.mem_iUnion] at hb
  obtain ⟨m, hm⟩ := hb
  simp only [levelSet, Set.mem_iUnion]
  exact ⟨m, iterate_mem_firstEntryLayer_sub (by nlinarith) hm⟩

theorem disjoint_levelSet {Ω : Type*} {T : Ω → Ω} {A : Set Ω} {n : ℕ} (_hn : 0 < n)
    {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    Disjoint (levelSet T A n i) (levelSet T A n j) := by
  apply Set.disjoint_iUnion_left.mpr
  intro m; apply Set.disjoint_iUnion_right.mpr; intro m'
  refine firstEntryLayer_pairwiseDisjoint _ _ ?_
  intro h
  rw [tsub_eq_iff_eq_add_of_le] at h
  · rw [tsub_add_eq_add_tsub (by nlinarith), eq_tsub_iff_add_eq_of_le] at h
    · exact hij (by nlinarith [show m = m' by nlinarith])
    · nlinarith
  · nlinarith

/-! ### Tower measure bound -/

theorem measure_towerUnion_kakutaniBase_ge
    (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A)
    {n : ℕ} (hn : 0 < n) :
    n * μ (kakutaniBase T A n) ≤ μ (towerUnion T (kakutaniBase T A n) n) := by
  have h_sum_le_union : (∑ i ∈ Finset.range n, μ (towerFloor T (kakutaniBase T A n) i)) ≤ μ (towerUnion T (kakutaniBase T A n) n) := by
    convert sum_measure_le_of_separated μ ( fun i : Fin n => towerFloor T ( kakutaniBase T A n ) i ) ( fun i : Fin n => levelSet T A n i ) ?_ ?_ ?_ using 1;
    · rw [ Finset.sum_range ];
    · congr ; ext ; simp +decide [ towerUnion ];
      exact ⟨ fun ⟨ i, hi, hi' ⟩ => ⟨ ⟨ i, hi ⟩, hi' ⟩, fun ⟨ i, hi' ⟩ => ⟨ i, i.2, hi' ⟩ ⟩;
    · exact fun i => levelSet_measurableSet ( show Measurable T from hT.measurable ) hA;
    · intro i _ j _ hij; exact disjoint_levelSet hn ( Fin.is_lt i ) ( Fin.is_lt j ) ( by simpa [ Fin.ext_iff ] using hij ) ;
    · exact fun i => towerFloor_kakutaniBase_subset_levelSet ( Fin.is_lt i );
  have h_floor_ge_base : ∀ i ∈ Finset.range n, μ (towerFloor T (kakutaniBase T A n) i) ≥ μ (kakutaniBase T A n) := by
    intro i hi;
    apply measure_image_iterate_ge μ T hT (kakutaniBase_measurableSet hT.measurable hA) i;
  exact le_trans ( by simpa using Finset.sum_le_sum h_floor_ge_base ) h_sum_le_union

/-! ### Basin -/

def basin (T : Ω → Ω) (A : Set Ω) : Set Ω := ⋃ k : ℕ, (T^[k]) ⁻¹' A

theorem basin_measurableSet {T : Ω → Ω} {A : Set Ω}
    (hT : Measurable T) (hA : MeasurableSet A) :
    MeasurableSet (basin T A) :=
  MeasurableSet.iUnion fun k => (hT.iterate k) hA

theorem basin_superset {Ω : Type*} {T : Ω → Ω} {A : Set Ω} : A ⊆ basin T A := by
  intro x hx; exact mem_iUnion.mpr ⟨0, by simpa⟩

theorem basin_eq_iUnion_firstEntryLayer {Ω : Type*} (T : Ω → Ω) (A : Set Ω) :
    basin T A = ⋃ k, firstEntryLayer T A k := by
  rw [iUnion_firstEntryLayer_eq]; rfl

theorem measure_basin_compl_compl_le (μ : Measure Ω) {T : Ω → Ω}
    (_hT : MeasurePreserving T μ μ) {S : Set Ω} (_hS : MeasurableSet S) :
    μ (basin T Sᶜ)ᶜ ≤ μ S := by
  exact MeasureTheory.measure_mono
    (by simp +decide [basin, Set.subset_def]; exact fun x hx => hx 0)

/-! ### KakutaniBase measure bound (corrected) -/

/-
The tower union of kakutaniBase is contained in basin \ A.
    Every tower floor is in some levelSet, which consists of
    firstEntryLayers at positive levels, hence in basin \ A.
-/
theorem towerUnion_kakutaniBase_subset_basin_diff
    {Ω : Type*} {T : Ω → Ω} {A : Set Ω} {n : ℕ} (hn : 0 < n) :
    towerUnion T (kakutaniBase T A n) n ⊆ basin T A \ A := by
  have h_disjoint : ∀ i < n, Disjoint (levelSet T A n i) A := by
    intro i hi
    have h_levelSet_subset : levelSet T A n i ⊆ basin T A \ A := by
      intro x hx
      simp [levelSet] at hx
      obtain ⟨m, hm⟩ := hx
      simp [firstEntryLayer] at hm;
      exact ⟨ Set.mem_iUnion.2 ⟨ ( m + 1 ) * n - i, hm.1 ⟩, hm.2 0 ( Nat.sub_pos_of_lt ( by nlinarith ) ) ⟩;
    exact Set.disjoint_left.mpr fun x hx hx' => h_levelSet_subset hx |>.2 hx';
  have h_subset : ∀ i < n, towerFloor T (kakutaniBase T A n) i ⊆ basin T A := by
    intro i hi
    have h_levelSet_subset_basin : levelSet T A n i ⊆ basin T A := by
      simp +decide [ levelSet, basin ];
      exact fun k => Set.subset_iUnion_of_subset _ ( firstEntryLayer_subset_preimage _ _ _ );
    exact Set.Subset.trans ( towerFloor_kakutaniBase_subset_levelSet hi ) h_levelSet_subset_basin;
  intro x hx
  obtain ⟨i, hi, hx_i⟩ : ∃ i < n, x ∈ towerFloor T (kakutaniBase T A n) i := by
    unfold towerUnion at hx; aesop;
  exact ⟨ h_subset i hi hx_i, fun hx_A => Set.disjoint_left.mp ( h_disjoint i hi ) ( towerFloor_kakutaniBase_subset_levelSet hi hx_i ) hx_A ⟩

-- Removed: exists_rokhlinTower_of_basin_large
-- Its hypothesis μ(A) + μ((basin T A)ᶜ) ≤ ε is too weak for n ≥ 2.
-- See Rejected.md #17. The direct proof path uses exists_tower_from_basin instead.

end Submission.RokhlinCore
import ChallengeDeps

open LeanEval.Dynamics
open MeasureTheory Set Function

namespace Submission.Helpers

variable {Ω : Type*} {T : Ω → Ω} {B : Set Ω} {n : ℕ}

/-! ## Basic lemmas about `towerFloor` -/

@[simp]
theorem towerFloor_zero : towerFloor T B 0 = B := by
  simp [towerFloor, iterate_zero]

theorem towerFloor_succ (k : ℕ) :
    towerFloor T B (k + 1) = T '' towerFloor T B k := by
  unfold towerFloor; rw [iterate_succ']; exact image_comp T (T^[k]) B

theorem towerFloor_def (k : ℕ) : towerFloor T B k = T^[k] '' B := rfl

theorem mem_towerFloor_iff {x : Ω} {k : ℕ} :
    x ∈ towerFloor T B k ↔ ∃ b ∈ B, T^[k] b = x := by
  simp [towerFloor]

@[simp]
theorem towerFloor_empty (k : ℕ) : towerFloor T (∅ : Set Ω) k = ∅ := by
  unfold towerFloor; simp

/-! ## Basic lemmas about `towerUnion` -/

theorem towerUnion_def :
    towerUnion T B n = ⋃ k ∈ Finset.range n, towerFloor T B k := rfl

@[simp]
theorem towerUnion_zero : towerUnion T B 0 = ∅ := by
  simp [towerUnion]

@[simp]
theorem towerUnion_one : towerUnion T B 1 = B := by
  simp [towerUnion, Finset.range_one]

theorem mem_towerUnion_iff {x : Ω} :
    x ∈ towerUnion T B n ↔ ∃ k, k < n ∧ x ∈ towerFloor T B k := by
  simp [towerUnion, Finset.mem_range]

theorem towerUnion_mono {m n : ℕ} (h : m ≤ n) :
    towerUnion T B m ⊆ towerUnion T B n := by
  intro x hx
  rw [mem_towerUnion_iff] at hx ⊢
  obtain ⟨k, hk, hxk⟩ := hx
  exact ⟨k, Nat.lt_of_lt_of_le hk h, hxk⟩

theorem towerUnion_univ_one : towerUnion T (univ : Set Ω) 1 = univ := by
  simp

/-! ## `IsRokhlinTower` lemmas -/

variable [MeasurableSpace Ω]

theorem IsRokhlinTower.measurableSet (h : IsRokhlinTower T B n) : MeasurableSet B :=
  h.1

theorem IsRokhlinTower.pairwiseDisjoint (h : IsRokhlinTower T B n) :
    (Finset.range n : Set ℕ).PairwiseDisjoint (towerFloor T B) :=
  h.2

theorem isRokhlinTower_one (hB : MeasurableSet B) : IsRokhlinTower T B 1 :=
  ⟨hB, by intro i hi j hj hij; simp at hi hj; omega⟩

theorem isRokhlinTower_empty (n : ℕ) : IsRokhlinTower T (∅ : Set Ω) n :=
  ⟨MeasurableSet.empty, by intro i _ j _ _; unfold towerFloor; simp⟩

/-! ## The `n = 1` case -/

theorem rokhlin_lemma_one (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {ε : ENNReal} (_hε : 0 < ε) :
    ∃ B : Set Ω, IsRokhlinTower T B 1 ∧ μ (towerUnion T B 1) ≥ 1 - ε :=
  ⟨univ, isRokhlinTower_one MeasurableSet.univ,
    by simp [towerUnion, Finset.range_one, towerFloor, iterate_zero, measure_univ]⟩

/-! ## The `ε ≥ 1` case (trivial) -/

theorem rokhlin_lemma_eps_ge_one (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (n : ℕ) (_hn : 1 ≤ n) {ε : ENNReal} (hε : 1 ≤ ε) :
    ∃ B : Set Ω, IsRokhlinTower T B n ∧ μ (towerUnion T B n) ≥ 1 - ε :=
  ⟨∅, isRokhlinTower_empty n, by rw [tsub_eq_zero_of_le hε]; exact zero_le _⟩

/-! ## MeasurePreserving iteration -/

theorem measurePreserving_iterate {μ : Measure Ω} (hT : MeasurePreserving T μ μ) (k : ℕ) :
    MeasurePreserving (T^[k]) μ μ :=
  hT.iterate k

theorem measure_preimage_iterate {μ : Measure Ω} (hT : MeasurePreserving T μ μ) (k : ℕ)
    {s : Set Ω} (hs : MeasurableSet s) :
    μ (T^[k] ⁻¹' s) = μ s :=
  (hT.iterate k).measure_preimage hs.nullMeasurableSet

end Submission.Helpers

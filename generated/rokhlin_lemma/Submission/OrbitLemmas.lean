import ChallengeDeps
import Submission.MeasurabilityLemmas

/-! ## Orbit segment lemmas for aperiodic maps

The set of points where an orbit segment of length `n` has collisions has measure zero.
-/

open LeanEval.Dynamics
open MeasureTheory Set Function

namespace Submission.OrbitLemmas

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-
For each positive `k`, the set `{x | T^[k] x = x}` has measure zero (from aperiodicity).
-/
omit [StandardBorelSpace Ω] in
theorem measure_fixedPts_iterate_eq_zero (μ : Measure Ω) (T : Ω → Ω)
    (hap : IsAperiodic T μ) (k : ℕ) (hk : 0 < k) :
    μ {x : Ω | T^[k] x = x} = 0 := by
  refine' MeasureTheory.measure_mono_null _ hap;
  exact fun x hx => ⟨ k, hk, hx ⟩

/-
The set of points where an orbit segment of length `n` has a collision
(i.e., `T^[i] x = T^[j] x` for some `0 ≤ i < j < n`) has measure zero.
-/
theorem measure_orbit_collision_eq_zero (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ) (n : ℕ) :
    μ {x : Ω | ∃ i j, i < j ∧ j < n ∧ T^[i] x = T^[j] x} = 0 := by
  -- The set of points where an orbit segment of length `n` has a collision is a finite union of sets of the form `{x | T^[i] x = T^[j] x}`.
  have h_union : {x | ∃ i j : ℕ, i < j ∧ j < n ∧ T^[i] x = T^[j] x} = ⋃ (i : ℕ) (hi : i < n) (j : ℕ) (hj : j < n) (hij : i < j), {x | T^[i] x = T^[j] x} := by
    ext x; simp [Set.mem_iUnion];
    exact ⟨ fun ⟨ i, j, hij, hjn, h ⟩ => ⟨ i, by linarith, j, hij, hjn, h ⟩, fun ⟨ i, hi, j, hij, hjn, h ⟩ => ⟨ i, j, hij, hjn, h ⟩ ⟩;
  -- By the properties of measure-preserving systems, we know that each set `{x | T^[i] x = T^[j] x}` has measure zero.
  have h_zero_measure : ∀ i j : ℕ, i < j → i < n → j < n → μ {x | T^[i] x = T^[j] x} = 0 := by
    intro i j hij hi hj;
    -- By the properties of measure-preserving systems, we know that each set `{x | T^[i] x = T^[j] x}` is the preimage of `{y | T^[j-i] y = y}` under `T^[i]`.
    have h_preimage : {x | T^[i] x = T^[j] x} = (T^[i]) ⁻¹' {y | T^[j-i] y = y} := by
      simp +decide [ ← Function.iterate_add_apply, hij.le ];
      exact Set.ext fun x => eq_comm;
    rw [ h_preimage, hT.iterate i |>.measure_preimage ];
    · exact measure_fixedPts_iterate_eq_zero μ T hap _ ( Nat.sub_pos_of_lt hij );
    · refine' MeasurableSet.nullMeasurableSet _;
      apply_rules [ MeasurabilityLemmas.measurableSet_fixedPts_iterate ];
      exact hT.measurable;
  exact h_union.symm ▸ MeasureTheory.measure_iUnion_null fun i => MeasureTheory.measure_iUnion_null fun hi => MeasureTheory.measure_iUnion_null fun j => MeasureTheory.measure_iUnion_null fun hj => MeasureTheory.measure_iUnion_null fun hij => h_zero_measure i j hij hi hj

/-
For a.e. `x`, the orbit segment `x, Tx, ..., T^[n-1] x` consists of distinct points.
-/
theorem ae_orbit_segment_injective (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ) (n : ℕ) :
    ∀ᵐ x ∂μ, ∀ i j, i < n → j < n → T^[i] x = T^[j] x → i = j := by
  convert MeasureTheory.measure_eq_zero_iff_ae_notMem.1 ( measure_orbit_collision_eq_zero μ T hT hap n ) using 1;
  ext x; simp [Set.mem_setOf_eq];
  grind

end Submission.OrbitLemmas
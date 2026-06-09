import ChallengeDeps

/-! ## Aperiodic measure-preserving maps have non-atomic measures

Under the hypotheses of the Rokhlin lemma, the measure `μ` has no atoms.

The proof splits into two cases:
1. If `x ∈ periodicPts T`, then `μ {x} ≤ μ (periodicPts T) = 0`.
2. If `x ∉ periodicPts T`, the orbit may NOT be injective (T might not be injective).
   However, the orbit is eventually periodic: there exist m < n with T^[m] x = T^[n] x.
   Then T^[m] x ∈ periodicPts T (with period n-m), so μ {T^[m] x} = 0.
   Since μ {x} ≤ μ {Tx} ≤ ... ≤ μ {T^[m] x} = 0, we get μ {x} = 0.
   Alternatively, the orbit visits infinitely many distinct points, and the sum argument works.

   Actually: if x ∉ periodicPts T, then for ALL k > 0, T^[k] x ≠ x.
   The orbit {x, Tx, T²x, ...} may have repeats among T^i x for i > 0,
   but x itself never recurs. Now μ {x} ≤ μ {Tx} ≤ μ {T²x} ≤ ...
   and these form a monotone sequence. Either the orbit visits infinitely many
   distinct points (then sum → ∞ if μ{x} > 0, contradiction), or eventually
   T^m x = T^n x with m < n, so T^m x is periodic, μ{T^m x} = 0, μ{x} = 0.
-/

open LeanEval.Dynamics
open MeasureTheory Set Function

namespace Submission.NoAtoms

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Measure-preserving maps are monotone on singletons: μ({x}) ≤ μ({T x}). -/
theorem measure_singleton_le_image (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (x : Ω) :
    μ {x} ≤ μ {T x} := by
  calc μ {x} ≤ μ (T ⁻¹' {T x}) := by
        apply measure_mono; intro y hy; simp at hy ⊢; exact congr_arg T hy
      _ = μ {T x} := hT.measure_preimage (measurableSet_singleton _).nullMeasurableSet

/-
Measure of a singleton under iterate: μ({x}) ≤ μ({T^[k] x}).
-/
theorem measure_singleton_le_iterate (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (x : Ω) (k : ℕ) :
    μ {x} ≤ μ {T^[k] x} := by
  exact measure_singleton_le_image μ (T^[k]) (hT.iterate k) x

/-
Periodic points have zero measure when T is aperiodic.
-/
omit [StandardBorelSpace Ω] in
theorem measure_singleton_periodic_eq_zero (μ : Measure Ω)
    (T : Ω → Ω) (hap : IsAperiodic T μ)
    (x : Ω) (hx : x ∈ periodicPts T) :
    μ {x} = 0 := by
  convert MeasureTheory.measure_mono_null ( Set.singleton_subset_iff.mpr hx ) hap using 1

/-
In a standard Borel probability space, an aperiodic measure-preserving map
gives rise to a non-atomic measure.
-/
theorem noAtoms_of_aperiodic (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ) :
    NoAtoms μ := by
  -- Consider any $x \in \Omega$.
  have h_zero_measure : ∀ x : Ω, μ {x} = 0 := by
    intro x
    by_contra h_nonzero
    have h_orbit : ∀ k : ℕ, μ {T^[k] x} ≥ μ {x} := by
      exact fun k => measure_singleton_le_iterate μ T hT x k
    -- Consider the function k ↦ T^k(x) on ℕ. Either it's injective on some infinite subset (giving an infinite set of distinct singletons each of measure ≥ μ{x}), or there exist 0 < m < n with T^m(x) = T^n(x). In the latter case, T^m(x) is periodic (IsPeriodicPt T (n-m) (T^m(x))), hence μ{T^m(x)} = 0, contradicting μ{T^m(x)} ≥ μ{x} > 0.
    by_cases h_inj : Set.InjOn (fun k => T^[k] x) (Set.univ : Set ℕ);
    · have h_inf : ∑' k : ℕ, μ {T^[k] x} ≤ μ (Set.univ : Set Ω) := by
        rw [ ← MeasureTheory.measure_iUnion ];
        · exact MeasureTheory.measure_mono ( Set.subset_univ _ );
        · exact fun i j hij => Set.disjoint_singleton.2 <| h_inj.ne ( Set.mem_univ i ) ( Set.mem_univ j ) hij;
        · exact fun i => measurableSet_singleton (T^[i] x)
      contrapose! h_inf;
      refine' lt_of_lt_of_le _ ( ENNReal.tsum_le_tsum h_orbit );
      simp +decide [ h_nonzero ];
    · -- Since the function k ↦ T^k(x) is not injective on ℕ, there exist 0 < m < n with T^m(x) = T^n(x).
      obtain ⟨m, n, hmn, h_eq⟩ : ∃ m n : ℕ, 0 < m ∧ m < n ∧ T^[m] x = T^[n] x := by
        obtain ⟨m, n, hmn, h_eq⟩ : ∃ m n : ℕ, m < n ∧ T^[m] x = T^[n] x := by
          simp_all +decide [ InjOn ];
          obtain ⟨ m, n, hmn, hne ⟩ := h_inj; exact hne |> fun h => by cases lt_trichotomy m n <;> tauto;
        refine' ⟨ m + 1, n + 1, Nat.succ_pos _, Nat.succ_lt_succ hmn, _ ⟩;
        rw [ Function.iterate_succ_apply', Function.iterate_succ_apply', h_eq ];
      -- Since $T^m(x) = T^n(x)$, we have $T^{n-m}(T^m(x)) = T^m(x)$, so $T^m(x)$ is periodic with period $n-m$.
      have h_periodic : Function.IsPeriodicPt T (n - m) (T^[m] x) := by
        rw [ Function.IsPeriodicPt, Function.IsFixedPt, ← Function.iterate_add_apply, Nat.sub_add_cancel h_eq.1.le, h_eq.2 ];
      exact absurd ( measure_singleton_periodic_eq_zero μ T hap ( T^[m] x ) ⟨ n - m, Nat.sub_pos_of_lt h_eq.1, h_periodic ⟩ ) ( ne_of_gt ( lt_of_lt_of_le ( pos_iff_ne_zero.mpr h_nonzero ) ( h_orbit m ) ) );
  exact { measure_singleton := h_zero_measure }

end Submission.NoAtoms
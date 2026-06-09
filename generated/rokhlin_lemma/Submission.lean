import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.OrbitLemmas
import Submission.MarkerLemmas
import Submission.MaximalTower
import Submission.Shadow
import Submission.RokhlinCore
import Submission.ResidueTower
import Submission.BasinCoverage
import Submission.ErgodicDecomp
import Submission.InvariantSigmaAlgebra
import Submission.CondExpInvariant
import Submission.MeanErgodic
import Submission.GeneralBasin
import Submission.BasinCondExp
import Submission.ZornInvariant
import Submission.CondNonAtomic
import Submission.KernelNonAtomic
import Submission.KernelInvariance
import Submission.MarkerConstruction

open LeanEval.Dynamics
open MeasureTheory Set

namespace Submission

open Submission.RokhlinCore Submission.ResidueTower Submission.BasinCoverage
open Submission.GeneralBasin

/-
Main reduction: given `exists_small_set_large_basin` and `exists_tower_from_basin`,
    prove the Rokhlin core lemma.
    Choose δ = ε/(2n), find A with μ(A) ≤ δ and μ((basin T A)ᶜ) ≤ δ.
    Then exists_tower_from_basin gives tower with
    μ(tower) ≥ μ(basin\A) - (n-1)μ(A) = 1 - μ(compl) - nμ(A) ≥ 1 - δ - nδ = 1 - (n+1)δ.
    Since δ = ε/(2n) and n ≥ 2: (n+1)/(2n) ≤ 1, so (n+1)δ ≤ ε.
-/
theorem rokhlin_core {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    (n : ℕ) (hn : 2 ≤ n) {ε : ENNReal} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ B : Set Ω, IsRokhlinTower T B n ∧
      μ (towerUnion T B n) ≥ 1 - ε := by
  -- Choose δ for the basin coverage lemma
  have hδ : (0 : ENNReal) < ε / (2 * n) := by
    apply ENNReal.div_pos hε.ne'
    exact (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top n))
  -- Get A with small measure and large basin
  obtain ⟨A, hA_meas, hA_small, hA_basin⟩ :=
    exists_small_set_large_basin_v2 μ T hT hap hδ
  -- Get tower from basin
  obtain ⟨B, hB_tower, hB_measure⟩ :=
    exists_tower_from_basin μ T hT hA_meas (by omega : 0 < n)
  refine ⟨B, hB_tower, ?_⟩
  -- Show μ(tower) ≥ 1 - ε
  -- We have: μ(tower) ≥ μ(basin T A \ A) - (n-1) * μ(A)
  -- And: μ(basin T A \ A) = μ(basin T A) - μ(A) ≥ 1 - δ - μ(A) ≥ 1 - 2δ
  -- And: (n-1) * μ(A) ≤ (n-1) * δ
  -- So: μ(tower) ≥ 1 - 2δ - (n-1)δ = 1 - (n+1)δ = 1 - (n+1)ε/(2n) ≥ 1 - ε
  refine' le_trans _ hB_measure;
  rw [ measure_diff ];
  · -- Using the bounds on the measures of the basin and A, we can simplify the inequality.
    have h_simplify : μ (basin T A) ≥ 1 - ε / (2 * n) ∧ μ A ≤ ε / (2 * n) := by
      have h_simplify : μ (basin T A) = 1 - μ (basin T A)ᶜ := by
        rw [ MeasureTheory.measure_compl ] <;> norm_num;
        · rw [ ENNReal.sub_sub_cancel ];
          · norm_num;
          · exact le_trans ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide );
        · apply_rules [ basin_measurableSet, hT.measurable ];
      exact ⟨ h_simplify.symm ▸ tsub_le_tsub_left hA_basin _, hA_small ⟩;
    refine' le_trans _ ( tsub_le_tsub ( tsub_le_tsub h_simplify.1 h_simplify.2 ) ( mul_le_mul_left' h_simplify.2 _ ) );
    rw [ tsub_tsub, tsub_tsub ];
    refine' tsub_le_tsub_left _ _;
    rw [ ← add_assoc, ← ENNReal.toReal_le_toReal ] <;> norm_num;
    · rw [ ENNReal.toReal_add, ENNReal.toReal_add ] <;> norm_num;
      · rw [ ENNReal.toReal_sub_of_le ] <;> norm_num;
        · field_simp;
          nlinarith [ show ( n : ℝ ) ≥ 2 by norm_cast, show ( ε.toReal : ℝ ) ≥ 0 by positivity ];
        · linarith;
      · exact ne_of_lt ( ENNReal.div_lt_top ( by aesop ) ( by aesop ) );
      · exact ne_of_lt ( ENNReal.div_lt_top ( by aesop ) ( by aesop ) );
      · exact ne_of_lt ( ENNReal.div_lt_top ( by aesop ) ( by aesop ) );
      · simp +decide [ ENNReal.mul_eq_top ];
        exact fun _ => ne_of_lt ( ENNReal.div_lt_top ( by aesop ) ( by aesop ) );
    · simp +decide [ ENNReal.mul_eq_top, ENNReal.div_eq_top ];
      exact ⟨ ⟨ fun _ => by positivity, by aesop ⟩, fun _ => ⟨ fun _ => by positivity, by aesop ⟩ ⟩;
    · exact ne_of_lt ( lt_of_lt_of_le hε1 ( by norm_num ) );
  · exact basin_superset;
  · exact hA_meas.nullMeasurableSet;
  · exact MeasureTheory.measure_ne_top _ _

theorem rokhlin_lemma {Ω : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (_hT : MeasurePreserving T μ μ) (_hap : IsAperiodic T μ)
    (n : ℕ) (_hn : 1 ≤ n) {ε : ENNReal} (_hε : 0 < ε) :
    ∃ B : Set Ω, IsRokhlinTower T B n ∧
      μ (towerUnion T B n) ≥ 1 - ε := by
  by_cases hε1 : 1 ≤ ε
  · exact Helpers.rokhlin_lemma_eps_ge_one μ T n _hn hε1
  push_neg at hε1
  by_cases hn1 : n = 1
  · subst hn1
    exact Helpers.rokhlin_lemma_one μ T _hε
  · have hn2 : 2 ≤ n := by omega
    exact rokhlin_core μ T _hT _hap n hn2 _hε hε1

end Submission
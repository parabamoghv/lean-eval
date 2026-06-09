import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.MeasurabilityLemmas
import Submission.NoAtoms
import Submission.SmallSets
import Submission.RokhlinCore
import Submission.BasinCoverage
import Submission.CondExpInvariant
import Submission.CondNonAtomic
import Submission.KernelInvariance
import Submission.CondExpHalving

/-!
# Kernel non-atomicity and marker construction
-/

open LeanEval.Dynamics
open MeasureTheory Set Function ProbabilityTheory
open Submission.RokhlinCore Submission.BasinCoverage Submission.CondExpInvariant
open Submission.CondNonAtomic Submission.KernelInvariance Submission.CondExpHalving
open Classical

noncomputable section

namespace Submission.KernelNonAtomic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-! ### condExp of periodicPts is zero a.e. -/

theorem condExp_periodicPts_zero
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ) :
    (μ[(periodicPts T).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) =ᵐ[μ] 0 := by
  convert MeasureTheory.condExp_congr_ae _
  rotate_left
  exact fun _ => 0
  · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hap ] with x hx using by aesop
  · rw [ MeasureTheory.condExp_of_stronglyMeasurable ] <;> norm_num
    · rfl
    · exact MeasureTheory.stronglyMeasurable_const

/-! ### Kernel splitting: non-atomic kernel means generators split non-trivially -/

/-
If ν is a non-atomic probability measure, A is measurable with ν(A) > 0,
    and G separates points with m₀ = generateFrom(range G), then
    there exists n with ν(A ∩ G n) ∈ (0, ν(A)).

    Proof: If for all n, ν(A ∩ G_n) ∈ {0, ν(A)}, then ν restricted to A
    concentrates on a single point (since generators separate). But ν has
    no atoms, contradiction.
-/
theorem exists_splitting_gen {ν : Measure Ω} [IsProbabilityMeasure ν]
    (hν_na : ∀ y : Ω, ν {y} = 0) (G : ℕ → Set Ω)
    (hG_meas : ∀ n, MeasurableSet (G n))
    (hG_gen : m₀ = MeasurableSpace.generateFrom (range G))
    (hG_sep : ∀ x y : Ω, x ≠ y → ∃ n, (x ∈ G n ∧ y ∉ G n) ∨ (x ∉ G n ∧ y ∈ G n))
    {A : Set Ω} (hA : MeasurableSet A) (hA_pos : ν A > 0) :
    ∃ n, ν (A ∩ G n) > 0 ∧ ν (A ∩ G n) < ν A := by
  -- Assume for contradiction that for all n, ν (A ∩ G n) ∈ {0, ν A}.
  by_contra h_contra
  have h_all : ∀ n, ν (A ∩ G n) = 0 ∨ ν (A ∩ G n) = ν A := by
    contrapose! h_contra;
    exact h_contra.imp fun n hn => ⟨ lt_of_le_of_ne ( zero_le _ ) ( Ne.symm hn.1 ), lt_of_le_of_ne ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) hn.2 ⟩;
  -- Let $B_N = A \cap \bigcap_{n \leq N} S_n$. Then $B_N$ is decreasing and $\nu(B_N) = \nu(A)$ for all $N$.
  obtain ⟨B, hB⟩ : ∃ B : ℕ → Set Ω, (∀ N, ν (B N) = ν A) ∧ (∀ N, MeasurableSet (B N)) ∧ (∀ N, B N ⊆ A) ∧ (∀ N, B (N + 1) ⊆ B N) ∧ (∀ N, ∀ x ∈ B N, ∀ y ∈ B N, ∀ n ≤ N, (x ∈ G n ↔ y ∈ G n)) := by
    refine' ⟨ fun N => A ∩ ⋂ n ≤ N, if ν ( A ∩ G n ) = ν A then G n else ( G n ) ᶜ, _, _, _, _, _ ⟩ <;> simp +decide [ hA, hG_meas ];
    · intro N;
      refine' le_antisymm ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) _;
      have h_inter : ν (A \ ⋂ n ≤ N, if ν (A ∩ G n) = ν A then G n else (G n)ᶜ) = 0 := by
        have hB_N : ∀ n ≤ N, ν (A \ (if ν (A ∩ G n) = ν A then G n else (G n)ᶜ)) = 0 := by
          intro n hn; specialize h_all n; split_ifs at * <;> simp_all +decide [ Set.diff_eq ] ;
          rw [ show A ∩ ( G n ) ᶜ = A \ ( A ∩ G n ) by ext; aesop, MeasureTheory.measure_diff ] <;> aesop;
        have hB_N : ν (⋃ n ≤ N, A \ (if ν (A ∩ G n) = ν A then G n else (G n)ᶜ)) = 0 := by
          exact MeasureTheory.measure_iUnion_null fun n => MeasureTheory.measure_iUnion_null fun hn => hB_N n hn;
        convert hB_N using 2 ; ext ; simp +decide [ Set.diff_iInter ];
      convert MeasureTheory.measure_mono ( show A ⊆ ( A ∩ ⋂ n ≤ N, if ν ( A ∩ G n ) = ν A then G n else ( G n ) ᶜ ) ∪ ( A \ ⋂ n ≤ N, if ν ( A ∩ G n ) = ν A then G n else ( G n ) ᶜ ) from fun x hx => by by_cases hx' : x ∈ ⋂ n ≤ N, if ν ( A ∩ G n ) = ν A then G n else ( G n ) ᶜ <;> aesop ) using 1 ; rw [ MeasureTheory.measure_union ] <;> norm_num [ h_inter ];
      · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₂.2 hx₁.2;
      · exact hA.diff ( MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => by split_ifs <;> [ exact hG_meas _; exact MeasurableSet.compl ( hG_meas _ ) ] );
      · infer_instance;
    · intro N; exact MeasurableSet.inter hA ( MeasurableSet.iInter fun n => MeasurableSet.iInter fun hn => by split_ifs <;> [ exact hG_meas n; exact MeasurableSet.compl ( hG_meas n ) ] ) ;
    · intro N i hi x hx; simp_all +decide [ Set.subset_def ] ;
      exact hx.2 i ( Nat.le_succ_of_le hi );
    · grind +ring;
  -- Since $B_N$ is decreasing and $\nu(B_N) = \nu(A) > 0$ for all $N$, we have $\nu(\bigcap_{N} B_N) = \nu(A) > 0$.
  have h_inter_pos : ν (⋂ N, B N) = ν A := by
    have h_inter_pos : Filter.Tendsto (fun N => ν (B N)) Filter.atTop (nhds (ν (⋂ N, B N))) := by
      apply_rules [ MeasureTheory.tendsto_measure_iInter_atTop ];
      · exact fun N => MeasurableSet.nullMeasurableSet ( hB.2.1 N );
      · exact antitone_nat_of_succ_le hB.2.2.2.1;
      · exact ⟨ 0, ne_of_lt ( MeasureTheory.measure_lt_top _ _ ) ⟩;
    exact tendsto_nhds_unique h_inter_pos ( by simpa only [ hB.1 ] using tendsto_const_nhds );
  -- Since $B_N$ is decreasing and $\nu(B_N) = \nu(A) > 0$ for all $N$, we have $\bigcap_{N} B_N \subseteq \{y\}$ for some $y$.
  obtain ⟨y, hy⟩ : ∃ y, ⋂ N, B N ⊆ {y} := by
    have h_inter_singleton : ∀ x y, x ∈ ⋂ N, B N → y ∈ ⋂ N, B N → x = y := by
      intro x y hx hy; specialize hG_sep x y; simp_all +decide [ Set.mem_iInter ] ;
      exact Classical.not_not.1 fun h => by obtain ⟨ n, hn ⟩ := hG_sep h; specialize hB; have := hB.2.2.2.2 n x ( hx n ) y ( hy n ) n le_rfl; aesop;
    exact Exists.elim ( MeasureTheory.nonempty_of_measure_ne_zero ( by rw [ h_inter_pos ] ; positivity ) ) fun x hx => ⟨ x, fun y hy => h_inter_singleton _ _ hy hx ⟩;
  exact absurd ( h_inter_pos ▸ MeasureTheory.measure_mono hy ) ( by aesop )

/-! ### Fiberwise splitting from kernel non-atomicity -/

/-
For a.e. ω with condExp(1_A|I_T)(ω) > 0, there exists a generator
    that non-trivially splits A within the fiber.
-/
theorem ae_exists_splitting_condExp [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {A : Set Ω} (hA : MeasurableSet A)
    (G : ℕ → Set Ω) (hG_meas : ∀ n, MeasurableSet (G n))
    (hG_gen : m₀ = MeasurableSpace.generateFrom (range G))
    (hG_sep : ∀ x y : Ω, x ≠ y → ∃ n, (x ∈ G n ∧ y ∉ G n) ∨ (x ∉ G n ∧ y ∈ G n)) :
    ∀ᵐ ω ∂μ,
      (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) ω > 0 →
      ∃ n, (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) ω > 0 ∧
           (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) ω <
           (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) ω := by
  have h_kernel_nonatomic : ∀ᵐ ω ∂μ, ∀ y : Ω, (condExpKernel μ (invSigmaAlgebra T) ω {y}) = 0 := by
    exact?;
  have h_kernel_real_eq_condExp : ∀ᵐ ω ∂μ, (μ[(A).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T] ω) = (condExpKernel μ (invSigmaAlgebra T) ω A).toReal := by
    convert kernel_real_eq_condExp μ T hA |> fun h => h.symm using 1;
  have h_kernel_real_eq_condExp_inter : ∀ n, ∀ᵐ ω ∂μ, (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T] ω) = (condExpKernel μ (invSigmaAlgebra T) ω (A ∩ G n)).toReal := by
    intro n;
    convert kernel_real_eq_condExp μ T ( hA.inter ( hG_meas n ) ) using 1;
    exact Filter.eventuallyEq_comm;
  filter_upwards [ h_kernel_nonatomic, h_kernel_real_eq_condExp, MeasureTheory.ae_all_iff.2 h_kernel_real_eq_condExp_inter ] with ω hω₁ hω₂ hω₃;
  intro h_pos
  obtain ⟨n, hn⟩ : ∃ n, (condExpKernel μ (invSigmaAlgebra T) ω (A ∩ G n)) > 0 ∧ (condExpKernel μ (invSigmaAlgebra T) ω (A ∩ G n)) < (condExpKernel μ (invSigmaAlgebra T) ω A) := by
    apply_rules [ exists_splitting_gen ];
    contrapose! h_pos; aesop;
  use n;
  simp_all +decide [ ENNReal.toReal_pos_iff ]

/-! ### Halving lemma -/

/-- Given A with condExp(1_A|I_T) > 0 a.e., there exists B with
    condExp(1_B|I_T) > 0 a.e. and μ(B) ≤ μ(A) / 2. -/
theorem condExp_halving [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {A : Set Ω} (hA : MeasurableSet A)
    (hA_pos : ∀ᵐ x ∂μ, 0 < (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) :
    ∃ B : Set Ω, MeasurableSet B ∧
      (∀ᵐ x ∂μ, 0 < (μ[B.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) ∧
      μ B ≤ μ A / 2 := by
  -- Step 1: Get separating generators
  obtain ⟨G, hG_meas, hG_gen, hG_sep⟩ := exists_separating_generators (m₀ := m₀)
  -- Step 2: Get the fiberwise splitting result
  have h_split := ae_exists_splitting_condExp μ T hT hap hA G hG_meas hG_gen hG_sep
  -- Step 3: Define h, g, and B via the halving construction
  set h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T] with h_def
  set g := fun n => μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T] with g_def
  set B := halvingChoice A G h g with B_def
  refine ⟨B, ?_, ?_, ?_⟩
  -- Step 4: B is measurable
  · exact halvingChoice_measurable hA hG_meas
      (stronglyMeasurable_condExp.measurable.comp (invSigmaAlgebra_le T))
      (fun n => (stronglyMeasurable_condExp.measurable.comp (invSigmaAlgebra_le T)))
  -- Step 5: condExp(1_B|I_T) > 0 a.e.
  · exact halvingChoice_condExp_pos μ T hA hG_meas h_split hA_pos
  -- Step 6: μ(B) ≤ μ(A)/2
  · exact halvingChoice_measure_bound μ T hA hG_meas

/-! ### Main marker theorem -/

/-
For any δ > 0, there exists A with μ(A) ≤ δ and condExp(1_A|I_T) > 0 a.e.
-/
theorem exists_small_condExp_pos_marker
    [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (hap : IsAperiodic T μ)
    {δ : ENNReal} (hδ : 0 < δ) :
    ∃ A : Set Ω, MeasurableSet A ∧ μ A ≤ δ ∧
      (∀ᵐ x ∂μ, 0 < (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
  cases' eq_or_ne δ ⊤ with h h;
  · refine' ⟨ Set.univ, MeasurableSet.univ, _, _ ⟩ <;> simp +decide [ h ];
    rw [ MeasureTheory.condExp_of_stronglyMeasurable ] <;> norm_num;
    exact stronglyMeasurable_const;
  · -- Choose k such that 1/2^k ≤ δ.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 / 2 : ENNReal) ^ k ≤ δ := by
      have h_lim : Filter.Tendsto (fun k : ℕ => (1 / 2 : ENNReal) ^ k) Filter.atTop (nhds 0) := by
        simp +zetaDelta at *;
      exact ( h_lim.eventually ( ge_mem_nhds hδ ) ) |> fun h => h.exists;
    -- By induction on $k$, we can construct a sequence of sets $A_k$ such that $\mu(A_k) \leq 1/2^k$ and $\text{condExp}(1_{A_k}|I_T) > 0$ a.e.
    have h_ind : ∀ k : ℕ, ∃ A : Set Ω, MeasurableSet A ∧ μ A ≤ (1 / 2 : ENNReal) ^ k ∧ (∀ᵐ x ∂μ, 0 < (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
      intro k;
      induction' k with k ih;
      · refine' ⟨ Set.univ, MeasurableSet.univ, _, _ ⟩ <;> norm_num;
        rw [ MeasureTheory.condExp_of_stronglyMeasurable ] <;> norm_num;
        exact stronglyMeasurable_const;
      · obtain ⟨ A, hA₁, hA₂, hA₃ ⟩ := ih;
        have := condExp_halving μ T hT hap hA₁ hA₃;
        obtain ⟨ B, hB₁, hB₂, hB₃ ⟩ := this; use B; simp_all +decide [ pow_succ, div_eq_mul_inv ] ;
        exact hB₃.trans ( mul_le_mul_right' hA₂ _ );
    exact Exists.elim ( h_ind k ) fun A hA => ⟨ A, hA.1, hA.2.1.trans hk, hA.2.2 ⟩

end Submission.KernelNonAtomic

end
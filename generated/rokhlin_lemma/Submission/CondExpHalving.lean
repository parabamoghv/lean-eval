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

/-!
# Helper lemmas for the condExp halving construction

Provides pull-out and difference lemmas for conditional expectation
of indicator functions with respect to the invariant σ-algebra,
and the key infrastructure for the halving argument.
-/

open LeanEval.Dynamics
open MeasureTheory Set Function ProbabilityTheory
open Submission.RokhlinCore Submission.BasinCoverage Submission.CondExpInvariant
open Submission.CondNonAtomic Submission.KernelInvariance
open Classical

noncomputable section

namespace Submission.CondExpHalving

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]

/-! ### Pull-out property for condExp of indicator intersections -/

theorem condExp_indicator_inter_invariant
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω)
    {S : Set Ω} (hS : MeasurableSet S) (hS_inv : T ⁻¹' S = S)
    {A : Set Ω} (hA : MeasurableSet A) :
    (μ[(S ∩ A).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T])
      =ᵐ[μ] fun x => S.indicator (fun x => (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) x := by
  have h_cond_exp : μ[(S ∩ A).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T] =ᵐ[μ] μ[S.indicator (A.indicator (fun _ => (1 : ℝ))) | invSigmaAlgebra T] := by
    convert Filter.EventuallyEq.rfl using 2 ; ext ; simp +decide [ Set.indicator ] ; aesop;
  refine' h_cond_exp.trans _;
  apply_rules [ MeasureTheory.condExp_indicator ];
  · exact MeasureTheory.integrable_indicator_iff hA |>.2 ( MeasureTheory.integrable_const _ );
  · exact ⟨ hS, hS_inv ⟩

theorem condExp_sdiff_indicator
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω)
    {A G : Set Ω} (hA : MeasurableSet A) (hG : MeasurableSet G) :
    (μ[(A \ G).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T])
      =ᵐ[μ] fun x => (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x -
                       (μ[(A ∩ G).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x := by
  convert MeasureTheory.condExp_sub _ _ using 3;
  any_goals exact μ;
  any_goals exact ℝ;
  any_goals try infer_instance;
  rotate_left;
  exact Set.indicator A fun _ => 1;
  exact Set.indicator ( A ∩ G ) fun _ => 1;
  · exact MeasureTheory.integrable_indicator_iff hA |>.2 ( MeasureTheory.integrable_const _ );
  · exact MeasureTheory.integrable_indicator_iff ( hA.inter hG ) |>.2 ( MeasureTheory.integrable_const _ );
  · constructor <;> intro h;
    · convert MeasureTheory.condExp_sub _ _ using 1;
      · exact MeasureTheory.integrable_indicator_iff hA |>.2 ( MeasureTheory.integrable_const _ );
      · exact MeasureTheory.integrable_indicator_iff ( hA.inter hG ) |>.2 ( MeasureTheory.integrable_const _ );
    · convert h ( invSigmaAlgebra T ) using 1;
      congr with x ; by_cases hx : x ∈ A <;> by_cases hx' : x ∈ G <;> simp +decide [ hx, hx' ]

theorem measure_eq_integral_condExp
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A) :
    (μ A).toReal = ∫ x, (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x ∂μ := by
  have h_integral_condExp : ∫ x, (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x ∂μ = ∫ x, (A.indicator (fun _ => (1 : ℝ))) x ∂μ := by
    apply_rules [ MeasureTheory.integral_condExp ];
  rw [ h_integral_condExp, MeasureTheory.integral_indicator ] <;> aesop

theorem measure_le_of_condExp_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hle : (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) ≤ᵐ[μ] g) :
    (μ A).toReal ≤ ∫ x, g x ∂μ := by
  refine' le_trans _ ( MeasureTheory.integral_mono_ae _ _ hle );
  · convert measure_eq_integral_condExp μ T hA |> le_of_eq;
  · apply_rules [ MeasureTheory.integrable_condExp ];
  · exact hg

/-! ### Separating generators from StandardBorelSpace -/

/-
In a StandardBorelSpace, there exists a countable family of measurable sets
    that generates the σ-algebra and separates points.
-/
theorem exists_separating_generators [StandardBorelSpace Ω] :
    ∃ G : ℕ → Set Ω,
      (∀ n, MeasurableSet (G n)) ∧
      m₀ = MeasurableSpace.generateFrom (range G) ∧
      (∀ x y : Ω, x ≠ y → ∃ n, (x ∈ G n ∧ y ∉ G n) ∨ (x ∉ G n ∧ y ∈ G n)) := by
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Set Ω, m₀ = MeasurableSpace.generateFrom (Set.range G) ∧ ∀ n, MeasurableSet (G n) := by
    obtain ⟨G, hG⟩ : ∃ G : Set (Set Ω), G.Countable ∧ m₀ = MeasurableSpace.generateFrom G ∧ ∀ S ∈ G, MeasurableSet S := by
      obtain ⟨G, hG⟩ : ∃ G : Set (Set Ω), G.Countable ∧ m₀ = MeasurableSpace.generateFrom G := by
        exact MeasurableSpace.CountablyGenerated.isCountablyGenerated;
      refine' ⟨ G, hG.1, hG.2, fun S hS => hG.2 ▸ MeasurableSpace.measurableSet_generateFrom hS ⟩;
    have := hG.1.exists_eq_range;
    rcases G.eq_empty_or_nonempty with ( rfl | hne ) <;> simp_all +decide;
    · refine' ⟨ fun _ => ∅, _, _ ⟩ <;> simp +decide;
    · grind;
  have h_sep : ∀ x y : Ω, x ≠ y → ∃ S : Set Ω, MeasurableSet S ∧ (x ∈ S ∧ y ∉ S ∨ x ∉ S ∧ y ∈ S) := by
    intro x y hxy;
    exact ⟨ { y }, by simp +decide, by simpa ⟩;
  contrapose! h_sep;
  obtain ⟨ x, y, hxy, h ⟩ := h_sep G hG.2 hG.1;
  refine' ⟨ x, y, hxy, fun S hS => _ ⟩;
  rw [ hG.1 ] at hS;
  induction hS;
  · grind;
  · simp +decide;
  · grind;
  · simp_all +decide [ Set.mem_iUnion ];
    grind +splitImp

/-! ### condExp positivity via condExp_mono -/

/-- If B ⊇ C, then condExp(1_B|m) ≥ condExp(1_C|m) a.e. -/
theorem condExp_indicator_mono
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω)
    {B C : Set Ω} (hB : @MeasurableSet _ m₀ B) (hC : @MeasurableSet _ m₀ C) (hBC : C ⊆ B) :
    (μ[C.indicator (fun _ => (1 : ℝ)) | m]) ≤ᵐ[μ]
    (μ[B.indicator (fun _ => (1 : ℝ)) | m]) :=
  condExp_mono
    (integrable_indicator_iff hC |>.2 (integrable_const _))
    (integrable_indicator_iff hB |>.2 (integrable_const _))
    (Filter.Eventually.of_forall (indicator_le_indicator_of_subset hBC (fun _ => zero_le_one)))

/-! ### Halving construction -/

/-- The priority region for generator n: where g_n first becomes non-trivial.
    D n = {0 < g_n < h} \ ⋃_{k < n} {0 < g_k < h}
    where g_n = condExp(1_{A ∩ G_n}|I_T) and h = condExp(1_A|I_T). -/
def priorityRegion (h : Ω → ℝ) (g : ℕ → Ω → ℝ) (n : ℕ) : Set Ω :=
  {x | 0 < g n x ∧ g n x < h x} \ ⋃ k ∈ Finset.range n, {x | 0 < g k x ∧ g k x < h x}

/-- The halving set: on each priority region, choose the smaller half. -/
def halvingChoice (A : Set Ω) (G : ℕ → Set Ω) (h : Ω → ℝ) (g : ℕ → Ω → ℝ) : Set Ω :=
  ⋃ n, ((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2})) ∪
       ((A \ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x}))

/-
Priority regions are pairwise disjoint.
-/
theorem priorityRegion_pairwise_disjoint (h : Ω → ℝ) (g : ℕ → Ω → ℝ) :
    Pairwise (Disjoint on priorityRegion h g) := by
  intro n m hnm;
  cases lt_or_gt_of_ne hnm <;> simp_all +decide [ Set.disjoint_left ]; all_goals unfold priorityRegion; aesop;

/-
Priority regions are I_T-measurable when h and g are condExp w.r.t. I_T.
-/
theorem priorityRegion_invSigmaAlgebra_measurable
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n)) (n : ℕ) :
    let h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let g := fun k => μ[(A ∩ G k).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    @MeasurableSet Ω (invSigmaAlgebra T) (priorityRegion h g n) := by
  apply_rules [ MeasurableSet.diff, MeasurableSet.iUnion ];
  · have h_meas : @Measurable _ _ (invSigmaAlgebra T) _ (fun x => (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) ∧ @Measurable _ _ (invSigmaAlgebra T) _ (fun x => (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
      constructor; all_goals apply_rules [ MeasureTheory.StronglyMeasurable.measurable, stronglyMeasurable_condExp ];
    exact measurableSet_lt measurable_const h_meas.1 |> MeasurableSet.inter <| measurableSet_lt h_meas.1 h_meas.2;
  · intro k
    apply_rules [ MeasurableSet.iUnion, MeasurableSet.inter, MeasurableSet.compl ];
    intro hk;
    have h_condExp_measurable : @Measurable Ω _ (invSigmaAlgebra T) _ (fun x => (μ[(A ∩ G k).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) ∧ @Measurable Ω _ (invSigmaAlgebra T) _ (fun x => (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
      constructor; all_goals apply_rules [ MeasureTheory.StronglyMeasurable.measurable, stronglyMeasurable_condExp ];
    exact measurableSet_lt measurable_const h_condExp_measurable.1 |> MeasurableSet.inter <| measurableSet_lt h_condExp_measurable.1 h_condExp_measurable.2

/-
Priority regions cover {h > 0} a.e., given the splitting result.
-/
theorem priorityRegion_cover_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {h : Ω → ℝ} {g : ℕ → Ω → ℝ}
    (h_split : ∀ᵐ ω ∂μ, h ω > 0 → ∃ n, 0 < g n ω ∧ g n ω < h ω) :
    ∀ᵐ ω ∂μ, h ω > 0 → ∃ n, ω ∈ priorityRegion h g n := by
  filter_upwards [ h_split ] with ω hω;
  intro hω_pos
  obtain ⟨n, hn⟩ := hω hω_pos
  use Nat.find (hω hω_pos);
  simp [priorityRegion];
  grind

/-
The halving choice set is measurable.
-/
theorem halvingChoice_measurable
    {A : Set Ω} (hA : MeasurableSet A)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    {h : Ω → ℝ} (hh : Measurable h)
    {g : ℕ → Ω → ℝ} (hg : ∀ n, Measurable (g n)) :
    MeasurableSet (halvingChoice A G h g) := by
  refine' MeasurableSet.iUnion _;
  intro n;
  refine' MeasurableSet.union _ _;
  · apply_rules [ MeasurableSet.inter, hA, hG ];
    · exact measurableSet_Ioi;
    · exact measurableSet_lt ( hg n ) hh;
    · exact MeasurableSet.compl ( MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_lt measurable_const ( hg _ ) |> MeasurableSet.inter <| measurableSet_lt ( hg _ ) hh );
    · exact measurableSet_le ( hg n ) ( hh.div_const _ );
  · refine' MeasurableSet.inter _ _;
    · exact hA.diff ( hG n );
    · refine' MeasurableSet.inter _ _;
      · refine' MeasurableSet.diff _ _;
        · exact measurableSet_lt measurable_const ( hg n ) |> MeasurableSet.inter <| measurableSet_lt ( hg n ) hh;
        · exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun hi => measurableSet_lt measurable_const ( hg i ) |> MeasurableSet.inter <| measurableSet_lt ( hg i ) hh;
      · exact measurableSet_lt ( hh.div_const _ ) ( hg n )

/-- Helper: each piece of halvingChoice is a subset. -/
theorem halvingChoice_subset_piece1 {A : Set Ω} {G : ℕ → Set Ω}
    {h : Ω → ℝ} {g : ℕ → Ω → ℝ} (n : ℕ) :
    (A ∩ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2}) ⊆ halvingChoice A G h g :=
  Set.subset_iUnion_of_subset n (Set.subset_union_left)

theorem halvingChoice_subset_piece2 {A : Set Ω} {G : ℕ → Set Ω}
    {h : Ω → ℝ} {g : ℕ → Ω → ℝ} (n : ℕ) :
    (A \ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x}) ⊆ halvingChoice A G h g :=
  Set.subset_iUnion_of_subset n (Set.subset_union_right)

/-
The condExp of the first piece on D_n ∩ H_n is g_n.
-/
theorem condExp_piece1_ae (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A) {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    (n : ℕ) :
    let h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let g := fun k => μ[(A ∩ G k).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let S := priorityRegion h g n ∩ {x | g n x ≤ h x / 2}
    (μ[(S ∩ (A ∩ G n)).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T])
      =ᵐ[μ] fun x => S.indicator (fun x => g n x) x := by
  apply_rules [ condExp_indicator_inter_invariant ];
  · apply_rules [ MeasurableSet.inter, MeasurableSet.compl ];
    · have h_measurable : Measurable (fun x => (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
        apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
        exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
      exact measurableSet_lt measurable_const h_measurable;
    · have h_measurable : Measurable (fun x => (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) ∧ Measurable (fun x => (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
        constructor <;> apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ]; all_goals exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
      exact measurableSet_lt h_measurable.1 h_measurable.2;
    · refine' MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hk => _;
      have h_measurable : Measurable (fun x => (μ[(A ∩ G k).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) ∧ Measurable (fun x => (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
        constructor;
        · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
          exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
        · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
          exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
      exact measurableSet_lt measurable_const h_measurable.1 |> MeasurableSet.inter <| measurableSet_lt h_measurable.1 h_measurable.2;
    · refine' measurableSet_le _ _;
      · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
        exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
      · refine' Measurable.mul _ measurable_const;
        apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
        exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
  · refine' measurableSet_invSigmaAlgebra_iff.mp _ |>.2;
    exact MeasurableSet.inter ( priorityRegion_invSigmaAlgebra_measurable μ T hA hG n ) ( measurableSet_le ( MeasureTheory.stronglyMeasurable_condExp.measurable ) ( MeasureTheory.stronglyMeasurable_condExp.measurable.div_const _ ) );
  · exact hA.inter ( hG n )

/-
The condExp of the second piece on D_n \ H_n is h - g_n.
-/
theorem condExp_piece2_ae (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A) {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    (n : ℕ) :
    let h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let g := fun k => μ[(A ∩ G k).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let S := priorityRegion h g n ∩ {x | h x / 2 < g n x}
    (μ[(S ∩ (A \ G n)).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T])
      =ᵐ[μ] fun x => S.indicator (fun x => h x - g n x) x := by
  have h_condExp_sdiff_indicator : (μ[(A \ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) =ᵐ[μ] (fun x => (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x - (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
    apply_rules [ condExp_sdiff_indicator ];
  have h_condExp_indicator_inter_invariant : ∀ {S : Set Ω}, @MeasurableSet Ω (invSigmaAlgebra T) S → (μ[(S ∩ (A \ G n)).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) =ᵐ[μ] (fun x => S.indicator (fun x => (μ[(A \ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) x) := by
    intro S hS
    apply condExp_indicator_inter_invariant;
    · exact hS.1;
    · exact hS.2;
    · exact hA.diff ( hG n );
  refine' Filter.EventuallyEq.trans ( h_condExp_indicator_inter_invariant _ ) _;
  · refine' MeasurableSet.inter _ _;
    · convert priorityRegion_invSigmaAlgebra_measurable μ T hA hG n using 1;
    · refine' measurableSet_lt _ _;
      · exact Measurable.mul ( MeasureTheory.stronglyMeasurable_condExp.measurable ) measurable_const;
      · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
  · exact Filter.EventuallyEq.indicator h_condExp_sdiff_indicator

theorem halvingChoice_condExp_pos
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    (h_split : ∀ᵐ ω ∂μ,
      (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) ω > 0 →
      ∃ n, (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) ω > 0 ∧
           (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) ω <
           (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) ω)
    (hA_pos : ∀ᵐ x ∂μ, 0 < (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) :
    let h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let g := fun n => μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let B := halvingChoice A G h g
    ∀ᵐ x ∂μ, 0 < (μ[B.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x := by
  intro h_split hA_pos
  set h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
  set g := fun n => μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
  set B := halvingChoice A G h g
  have h_cover : ∀ᵐ x ∂μ, h x > 0 → ∃ n, x ∈ priorityRegion h g n := by
    apply priorityRegion_cover_ae;
    · exact T;
    · exact h_split;
  have h_condExp_mono : ∀ n, ∀ᵐ x ∂μ, (μ[(priorityRegion h g n ∩ {x | g n x ≤ h x / 2} ∩ (A ∩ G n)).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x ≤ (μ[B.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x := by
    intro n
    have h_subset : priorityRegion h g n ∩ {x | g n x ≤ h x / 2} ∩ (A ∩ G n) ⊆ B := by
      exact fun x hx => Set.mem_iUnion.2 ⟨ n, Or.inl ⟨ by aesop, by aesop ⟩ ⟩;
    apply_rules [ condExp_indicator_mono ];
    · apply_rules [ halvingChoice_measurable ];
      · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
        exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
      · intro n; exact (by
        apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
        exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T ));
    · apply_rules [ MeasurableSet.inter, MeasurableSet.compl ];
      · have h_meas : Measurable (fun x => g n x) := by
          apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
          exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
        exact measurableSet_lt measurable_const h_meas;
      · have h_measurable : Measurable (fun x => g n x) ∧ Measurable (fun x => h x) := by
          constructor;
          · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
            exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
          · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
            exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
        exact measurableSet_lt h_measurable.1 h_measurable.2;
      · refine' MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hk => _;
        have h_measurable : Measurable (fun x => g k x) ∧ Measurable (fun x => h x) := by
          constructor;
          · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
            exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
          · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
            exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
        exact measurableSet_lt measurable_const h_measurable.1 |> MeasurableSet.inter <| measurableSet_lt h_measurable.1 h_measurable.2;
      · have h_measurable : Measurable (fun x => g n x) ∧ Measurable (fun x => h x) := by
          constructor;
          · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
            exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
          · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
            exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
        exact measurableSet_le h_measurable.1 ( h_measurable.2.div_const _ );
  have h_condExp_mono2 : ∀ n, ∀ᵐ x ∂μ, (μ[(priorityRegion h g n ∩ {x | h x / 2 < g n x} ∩ (A \ G n)).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x ≤ (μ[B.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x := by
    intro n
    apply condExp_indicator_mono μ (invSigmaAlgebra T) (by
    apply_rules [ halvingChoice_measurable ];
    · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
      exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
    · intro n; exact (by
      apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
      exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T ))) (by
    apply_rules [ MeasurableSet.inter, MeasurableSet.diff, hA, hG ];
    · have h_condExp_measurable : Measurable (fun x => (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
        apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
        exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
      exact measurableSet_lt measurable_const h_condExp_measurable;
    · have h_measurable : Measurable (fun x => g n x) ∧ Measurable (fun x => h x) := by
        constructor;
        · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
          exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
        · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
          exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
      exact measurableSet_lt h_measurable.1 h_measurable.2;
    · apply_rules [ MeasurableSet.iUnion, MeasurableSet.compl ];
      intro k; exact MeasurableSet.iUnion fun _ => MeasurableSet.inter ( measurableSet_lt measurable_const ( show Measurable ( g k ) from by
                                                                                                              apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
                                                                                                              exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T ) ) ) ( measurableSet_lt ( show Measurable ( g k ) from by
                                                                                                                                                                              apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
                                                                                                                                                                              exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T ) ) ( show Measurable h from by
                                                                                                                                                                                                                        apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
                                                                                                                                                                                                                        exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T ) ) ) ;
    · apply_rules [ MeasurableSet.mem, measurableSet_lt ];
      · apply_rules [ Measurable.mul, Measurable.div, measurable_const ];
        apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
        exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
      · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
        exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
    · exact MeasurableSet.compl ( hG n )) (by
    exact fun x hx => Set.mem_iUnion.2 ⟨ n, Or.inr ⟨ hx.2, hx.1 ⟩ ⟩);
  have h_condExp_eq : ∀ n, ∀ᵐ x ∂μ, (μ[(priorityRegion h g n ∩ {x | g n x ≤ h x / 2} ∩ (A ∩ G n)).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x = (priorityRegion h g n ∩ {x | g n x ≤ h x / 2}).indicator (fun x => g n x) x := by
    intro n
    apply condExp_piece1_ae μ T hA hG n;
  have h_condExp_eq2 : ∀ n, ∀ᵐ x ∂μ, (μ[(priorityRegion h g n ∩ {x | h x / 2 < g n x} ∩ (A \ G n)).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x = (priorityRegion h g n ∩ {x | h x / 2 < g n x}).indicator (fun x => h x - g n x) x := by
    intro n
    apply condExp_piece2_ae μ T hA hG n;
  filter_upwards [ hA_pos, h_cover, MeasureTheory.ae_all_iff.2 h_condExp_mono, MeasureTheory.ae_all_iff.2 h_condExp_mono2, MeasureTheory.ae_all_iff.2 h_condExp_eq, MeasureTheory.ae_all_iff.2 h_condExp_eq2 ] with x hx₁ hx₂ hx₃ hx₄ hx₅ hx₆;
  simp_all +decide [ Set.indicator ];
  grind +locals

/-
B ⊆ A.
-/
theorem halvingChoice_subset_A {A : Set Ω} {G : ℕ → Set Ω}
    {h : Ω → ℝ} {g : ℕ → Ω → ℝ} :
    halvingChoice A G h g ⊆ A := by
  intro x hx
  simp [halvingChoice] at hx
  obtain ⟨n, hn⟩ := hx
  aesop

/-
If condExp(1_C|I_T) =ᵐ S.indicator(f) and condExp(1_C'|I_T) =ᵐ S.indicator(g)
    with f ≤ g on S, then μ(C) ≤ μ(C').
-/
theorem measure_le_of_condExp_indicator_ae
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {C C' S : Set Ω} (hC : MeasurableSet C) (hC' : MeasurableSet C')
    {f g : Ω → ℝ}
    (hf : (μ[C.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) =ᵐ[μ] fun x => S.indicator f x)
    (hg : (μ[C'.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) =ᵐ[μ] fun x => S.indicator g x)
    (hfg : ∀ x, x ∈ S → f x ≤ g x)
    (hg_int : Integrable (fun x => S.indicator g x) μ) :
    μ C ≤ μ C' := by
  convert measure_le_of_condExp_le μ T hC _ _;
  any_goals exact hg_int;
  · rw [ ← MeasureTheory.integral_congr_ae hg, MeasureTheory.integral_condExp ];
    rw [ MeasureTheory.integral_indicator ] <;> norm_num [ hC', MeasureTheory.measureReal_def ];
  · filter_upwards [ hf, hg ] with x hx₁ hx₂;
    by_cases hx₃ : x ∈ S <;> simp_all +decide [ Set.indicator ]

/-! ### Generalized condExp identities for arbitrary invariant subsets -/

/-
For any invSigmaAlgebra-measurable S:
    condExp(1_{S ∩ (A ∩ G n)} | I_T) =ᵃᵉ S.indicator(g n).
-/
theorem condExp_inter_agn_general
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A) {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    (n : ℕ) {S : Set Ω} (hS : @MeasurableSet Ω (invSigmaAlgebra T) S) :
    (μ[(S ∩ (A ∩ G n)).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T])
      =ᵐ[μ] fun x => S.indicator
        (fun x => (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) x := by
  convert condExp_indicator_inter_invariant μ T _ _ _ using 1;
  · exact hS.1;
  · cases hS ; tauto;
  · exact hA.inter ( hG n )

/-
For any invSigmaAlgebra-measurable S:
    condExp(1_{S ∩ (A \ G n)} | I_T) =ᵃᵉ S.indicator(h - g n).
-/
theorem condExp_inter_sdiff_general
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A) {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    (n : ℕ) {S : Set Ω} (hS : @MeasurableSet Ω (invSigmaAlgebra T) S) :
    (μ[(S ∩ (A \ G n)).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T])
      =ᵐ[μ] fun x => S.indicator
        (fun x => (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x -
                  (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) x := by
  have h_indicator : (μ[(S ∩ (A \ G n)).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T])
      =ᵐ[μ] fun x => S.indicator
        (fun x => (μ[(A \ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) x := by
          convert condExp_inter_agn_general μ T _ _ _ _ using 1;
          rotate_left;
          rotate_left;
          exact Set.univ;
          all_goals norm_num [ Set.indicator ];
          use fun n => A \ G n;
          exact fun n => hA.diff ( hG n );
          exacts [ n, S, hS, rfl, rfl ];
  refine' h_indicator.trans _;
  filter_upwards [ condExp_sdiff_indicator μ T hA ( hG n ) ] with x hx using by by_cases hxS : x ∈ S <;> simp +decide [ hxS, hx ] ;

/-! ### Measure comparison lemmas for halvingChoice -/

/-
{g n ≤ h/2} is invSigmaAlgebra-measurable when g n, h are condExp.
-/
theorem halfRegion_le_invSigmaAlgebra_measurable
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    (n : ℕ) :
    let h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let g := fun k => μ[(A ∩ G k).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    @MeasurableSet Ω (invSigmaAlgebra T) {x | g n x ≤ h x / 2} := by
  refine' measurableSet_le _ _;
  · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
  · refine' Measurable.mul_const _ _;
    exact MeasureTheory.StronglyMeasurable.measurable ( MeasureTheory.stronglyMeasurable_condExp )

/-
{h/2 < g n} is invSigmaAlgebra-measurable when g n, h are condExp.
-/
theorem halfRegion_lt_invSigmaAlgebra_measurable
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    (n : ℕ) :
    let h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let g := fun k => μ[(A ∩ G k).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    @MeasurableSet Ω (invSigmaAlgebra T) {x | h x / 2 < g n x} := by
  apply_rules [ measurableSet_lt, measurable_const ];
  · exact Measurable.mul ( MeasureTheory.StronglyMeasurable.measurable ( MeasureTheory.stronglyMeasurable_condExp ) ) measurable_const;
  · apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ]

/-- On {g n ≤ h/2}: μ(A∩G n piece) ≤ μ(A\G n piece) -/
theorem piece_measure_comparison_part1
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    (n : ℕ) :
    let h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let g := fun k => μ[(A ∩ G k).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    μ ((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2}))
      ≤ μ ((A \ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2})) := by
  intro h g
  set S := priorityRegion h g n ∩ {x | g n x ≤ h x / 2} with hS_def
  have hS_inv : @MeasurableSet Ω (invSigmaAlgebra T) S :=
    MeasurableSet.inter (priorityRegion_invSigmaAlgebra_measurable μ T hA hG n)
      (halfRegion_le_invSigmaAlgebra_measurable μ T hA hG n)
  rw [Set.inter_comm (A ∩ G n), Set.inter_comm (A \ G n)]
  exact measure_le_of_condExp_indicator_ae μ T
    (hS_inv.1.inter (hA.inter (hG n)))
    (hS_inv.1.inter (hA.diff (hG n)))
    (condExp_inter_agn_general μ T hA hG n hS_inv)
    (condExp_inter_sdiff_general μ T hA hG n hS_inv)
    (fun x hx => by simp [S, priorityRegion] at hx; linarith [hx.2])
    ((integrable_condExp.sub integrable_condExp).indicator hS_inv.1)

/-- On {h/2 < g n}: μ(A\G n piece) ≤ μ(A∩G n piece) -/
theorem piece_measure_comparison_part2
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    (n : ℕ) :
    let h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let g := fun k => μ[(A ∩ G k).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    μ ((A \ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x}))
      ≤ μ ((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x})) := by
  intro h g
  set S := priorityRegion h g n ∩ {x | h x / 2 < g n x} with hS_def
  have hS_inv : @MeasurableSet Ω (invSigmaAlgebra T) S :=
    MeasurableSet.inter (priorityRegion_invSigmaAlgebra_measurable μ T hA hG n)
      (halfRegion_lt_invSigmaAlgebra_measurable μ T hA hG n)
  rw [Set.inter_comm (A \ G n), Set.inter_comm (A ∩ G n)]
  exact measure_le_of_condExp_indicator_ae μ T
    (hS_inv.1.inter (hA.diff (hG n)))
    (hS_inv.1.inter (hA.inter (hG n)))
    (condExp_inter_sdiff_general μ T hA hG n hS_inv)
    (condExp_inter_agn_general μ T hA hG n hS_inv)
    (fun x hx => by simp [S, priorityRegion] at hx; linarith [hx.2])
    (integrable_condExp.indicator hS_inv.1)

/-
The complement pieces are subsets of A \ B.
-/
theorem comp_subset_sdiff
    {A : Set Ω} {G : ℕ → Set Ω}
    {h : Ω → ℝ} {g : ℕ → Ω → ℝ} (n : ℕ) :
    (A \ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2}) ⊆ A \ halvingChoice A G h g ∧
    (A ∩ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x}) ⊆ A \ halvingChoice A G h g := by
  simp_all +decide [ Set.subset_def, Set.mem_diff, Set.mem_inter_iff, Set.mem_union, halvingChoice ];
  constructor <;> intro x hx₁ hx₂ hx₃ hx₄ m <;> constructor <;> contrapose! hx₄ <;> simp_all +decide [ priorityRegion ];
  · grind +ring;
  · grind;
  · grind +extAll;
  · grind +ring

/-
Each component of B has measure ≤ its complement component.
-/
theorem per_n_measure_le
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    (n : ℕ) :
    let h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let g := fun k => μ[(A ∩ G k).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    μ (((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2})) ∪
         ((A \ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x})))
      ≤ μ (((A \ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2})) ∪
           ((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x}))) := by
  convert MeasureTheory.measure_union_le _ _ |> le_trans <| add_le_add ( piece_measure_comparison_part1 μ T hA hG n ) ( piece_measure_comparison_part2 μ T hA hG n ) using 1;
  rw [ MeasureTheory.measure_union ];
  · exact Set.disjoint_left.mpr fun x hx₁ hx₂ => hx₁.1.2 hx₂.1.2;
  · apply_rules [ MeasurableSet.inter, MeasurableSet.union, MeasurableSet.compl, MeasurableSet.iUnion, MeasurableSet.iInter ];
    · have h_measurable : Measurable (fun x => (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
        apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ];
        exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
      exact measurableSet_lt measurable_const h_measurable;
    · have h_condExp_measurable : Measurable (fun x => (μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) ∧ Measurable (fun x => (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
        constructor <;> apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ]; all_goals exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
      exact measurableSet_lt h_condExp_measurable.1 h_condExp_measurable.2;
    · intro k; apply_rules [ MeasurableSet.iUnion, MeasurableSet.inter, MeasurableSet.compl ] ;
      intro hk;
      have h_measurable : Measurable (fun x => (μ[(A ∩ G k).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) ∧ Measurable (fun x => (μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]) x) := by
        constructor <;> apply_rules [ MeasureTheory.StronglyMeasurable.measurable, MeasureTheory.stronglyMeasurable_condExp ]; all_goals exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
      exact measurableSet_lt measurable_const h_measurable.1 |> MeasurableSet.inter <| measurableSet_lt h_measurable.1 h_measurable.2;
    · apply_rules [ MeasureTheory.StronglyMeasurable.measurableSet_lt, MeasureTheory.StronglyMeasurable.const_mul ];
      · apply_rules [ StronglyMeasurable.mul, stronglyMeasurable_const ];
        exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T );
      · exact MeasureTheory.StronglyMeasurable.mono ( MeasureTheory.stronglyMeasurable_condExp ) ( invSigmaAlgebra_le T )

/-
F(n) and C(n) are subsets of priorityRegion h g n
-/
theorem component_subset_priorityRegion
    {A : Set Ω} {G : ℕ → Set Ω}
    {h : Ω → ℝ} {g : ℕ → Ω → ℝ} (n : ℕ) :
    ((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2})) ∪
    ((A \ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x})) ⊆ priorityRegion h g n ∧
    ((A \ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2})) ∪
    ((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x})) ⊆ priorityRegion h g n := by
  grind

/-
The F-components are measurable
-/
theorem f_component_measurable
    {A : Set Ω} (hA : MeasurableSet A)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    {h : Ω → ℝ} (hh : Measurable h)
    {g : ℕ → Ω → ℝ} (hg : ∀ n, Measurable (g n))
    (n : ℕ) :
    MeasurableSet (((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2})) ∪
      ((A \ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x}))) := by
  apply_rules [ MeasurableSet.union, MeasurableSet.inter, hA, hG, MeasurableSet.compl ];
  any_goals exact measurableSet_lt measurable_const measurable_id';
  exact measurableSet_lt ( hg n ) hh;
  · exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun hi => measurableSet_lt measurable_const ( hg i ) |> MeasurableSet.inter <| measurableSet_lt ( hg i ) hh;
  · exact measurableSet_le ( hg n ) ( hh.div_const _ );
  · exact measurableSet_lt ( hg n ) hh;
  · exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun hi => measurableSet_lt measurable_const ( hg i ) |> MeasurableSet.inter <| measurableSet_lt ( hg i ) hh;
  · exact measurableSet_lt ( hh.div_const _ ) ( hg n )

/-
The complement components are measurable
-/
theorem comp_component_measurable
    {A : Set Ω} (hA : MeasurableSet A)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n))
    {h : Ω → ℝ} (hh : Measurable h)
    {g : ℕ → Ω → ℝ} (hg : ∀ n, Measurable (g n))
    (n : ℕ) :
    MeasurableSet (((A \ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2})) ∪
      ((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x}))) := by
  refine' MeasurableSet.union _ _;
  · refine' MeasurableSet.inter ( hA.diff ( hG n ) ) _;
    refine' MeasurableSet.inter _ _;
    · exact MeasurableSet.diff ( MeasurableSet.inter ( measurableSet_lt measurable_const ( hg n ) ) ( measurableSet_lt ( hg n ) hh ) ) ( MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hk => MeasurableSet.inter ( measurableSet_lt measurable_const ( hg k ) ) ( measurableSet_lt ( hg k ) hh ) );
    · exact measurableSet_le ( hg n ) ( hh.div_const _ );
  · apply_rules [ MeasurableSet.inter, MeasurableSet.union, MeasurableSet.compl, hA, hG ];
    · exact measurableSet_Ioi;
    · exact measurableSet_lt ( hg n ) hh;
    · exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun hi => measurableSet_lt measurable_const ( hg i ) |> MeasurableSet.inter <| measurableSet_lt ( hg i ) hh;
    · exact measurableSet_lt ( hh.div_const _ ) ( hg n )

/-- μ(B) ≤ μ(A \ B) from the piecewise comparisons. -/
theorem halvingChoice_le_compl
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n)) :
    let h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let g := fun k => μ[(A ∩ G k).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let B := halvingChoice A G h g
    μ B ≤ μ (A \ B) := by
  intro h g B
  set F := fun n => ((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2})) ∪
                    ((A \ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x}))
  set C := fun n => ((A \ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2})) ∪
                    ((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x}))
  have hh : Measurable h := stronglyMeasurable_condExp.measurable.comp (invSigmaAlgebra_le T)
  have hg_meas : ∀ n, Measurable (g n) :=
    fun n => stronglyMeasurable_condExp.measurable.comp (invSigmaAlgebra_le T)
  have hB_eq : B = ⋃ n, F n := rfl
  have hF_disj : Pairwise (Disjoint on F) := by
    intro n m hnm
    exact Disjoint.mono (component_subset_priorityRegion n).1 (component_subset_priorityRegion m).1
      (priorityRegion_pairwise_disjoint h g hnm)
  have hC_disj : Pairwise (Disjoint on C) := by
    intro n m hnm
    exact Disjoint.mono (component_subset_priorityRegion n).2 (component_subset_priorityRegion m).2
      (priorityRegion_pairwise_disjoint h g hnm)
  have hC_sub : ⋃ n, C n ⊆ A \ B := by
    apply Set.iUnion_subset; intro n
    exact Set.union_subset (comp_subset_sdiff n).1 (comp_subset_sdiff n).2
  have hFn_le : ∀ n, μ (F n) ≤ μ (C n) := fun n => per_n_measure_le μ T hA hG n
  have hF_meas : ∀ n, MeasurableSet (F n) :=
    fun n => f_component_measurable hA hG hh hg_meas n
  have hC_meas : ∀ n, MeasurableSet (C n) := fun n => comp_component_measurable hA hG hh hg_meas n
  calc μ B = μ (⋃ n, F n) := by rw [hB_eq]
    _ = ∑' n, μ (F n) := measure_iUnion hF_disj hF_meas
    _ ≤ ∑' n, μ (C n) := ENNReal.tsum_le_tsum hFn_le
    _ = μ (⋃ n, C n) := (measure_iUnion hC_disj hC_meas).symm
    _ ≤ μ (A \ B) := measure_mono hC_sub

/-- Measure bound: μ(B) ≤ μ(A)/2. -/
theorem halvingChoice_measure_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    {A : Set Ω} (hA : MeasurableSet A)
    {G : ℕ → Set Ω} (hG : ∀ n, MeasurableSet (G n)) :
    let h := μ[A.indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let g := fun n => μ[(A ∩ G n).indicator (fun _ => (1 : ℝ)) | invSigmaAlgebra T]
    let B := halvingChoice A G h g
    μ B ≤ μ A / 2 := by
  intro h g B
  -- Step 1: B ⊆ A
  have hB_sub : B ⊆ A := halvingChoice_subset_A
  -- Step 2: For each n, μ(piece1) ≤ μ(comp1) and μ(piece2) ≤ μ(comp2)
  -- piece1 = (A ∩ G n) ∩ (D_n ∩ H_n), comp1 = (A \ G n) ∩ (D_n ∩ H_n)
  -- piece2 = (A \ G n) ∩ (D_n \ H_n), comp2 = (A ∩ G n) ∩ (D_n \ H_n)
  have h_piece_le : ∀ n,
      μ ((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2}))
        ≤ μ ((A \ G n) ∩ (priorityRegion h g n ∩ {x | g n x ≤ h x / 2})) ∧
      μ ((A \ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x}))
        ≤ μ ((A ∩ G n) ∩ (priorityRegion h g n ∩ {x | h x / 2 < g n x})) :=
    fun n => ⟨piece_measure_comparison_part1 μ T hA hG n, piece_measure_comparison_part2 μ T hA hG n⟩
  -- Step 3: μ(B) ≤ μ(A \ B)
  have h_le_compl : μ B ≤ μ (A \ B) :=
    halvingChoice_le_compl μ T hA hG
  -- Step 4: μ(B) + μ(A \ B) ≤ μ(A)
  have hBmeas : MeasurableSet B := halvingChoice_measurable hA (fun n => hG n)
    (stronglyMeasurable_condExp.measurable.comp (invSigmaAlgebra_le T))
    (fun n => stronglyMeasurable_condExp.measurable.comp (invSigmaAlgebra_le T))
  have h_sum : μ B + μ (A \ B) ≤ μ A := by
    rw [← measure_union disjoint_sdiff_self_right (hA.diff hBmeas)]
    exact measure_mono (Set.union_subset hB_sub Set.diff_subset)
  -- Step 5: 2μ(B) ≤ μ(A), hence μ(B) ≤ μ(A)/2
  have h2 : μ B + μ B ≤ μ A :=
    le_trans (add_le_add_left h_le_compl (μ B)) (by rwa [add_comm] at h_sum)
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  rw [mul_comm]; rwa [two_mul]

end Submission.CondExpHalving

end
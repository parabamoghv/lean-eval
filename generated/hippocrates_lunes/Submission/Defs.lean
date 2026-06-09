import ChallengeDeps

open LeanEval.Geometry.HippocratesLunes
open MeasureTheory

namespace Submission.Helpers

/-- The semicircle on the horizontal leg (lower half). -/
abbrev hSemidisk (a : ℝ) : Set Plane :=
  closedHalfDisk A (B a) (fun t => t ≤ 0)

/-- The semicircle on the vertical leg (left half). -/
abbrev vSemidisk (b : ℝ) : Set Plane :=
  closedHalfDisk A (C b) (fun t => 0 ≤ t)

lemma measurableSet_hSemidisk (a : ℝ) : MeasurableSet (hSemidisk a) := by
  refine' MeasurableSet.inter _ _
  · have h_cont : Continuous (fun x : Plane => euclideanDistSq x (midpoint A (B a))) :=
      Continuous.add (Continuous.pow (continuous_fst.sub continuous_const) 2)
        (Continuous.pow (continuous_snd.sub continuous_const) 2)
    exact measurableSet_le h_cont.measurable measurable_const
  · unfold det2 vec A B; norm_num [Set.preimage]
    exact measurableSet_le (measurable_const.mul measurable_snd) measurable_const

lemma measurableSet_vSemidisk (b : ℝ) : MeasurableSet (vSemidisk b) := by
  refine' MeasurableSet.inter _ _
  · exact measurableSet_le
      (show Measurable fun x : Plane => euclideanDistSq x (midpoint A (C b)) from
        Continuous.measurable <| by continuity) measurable_const
  · exact measurableSet_le measurable_const
      (show Measurable fun x : Plane => det2 (vec A (C b)) (vec A x) from
        Continuous.measurable (by unfold det2 vec A C; continuity))

lemma measurableSet_hypotenuseSemidisk (a b : ℝ) :
    MeasurableSet (hypotenuseSemidisk a b) := by
  refine' MeasurableSet.inter _ _
  · have h_cont : Continuous (fun x : Plane => euclideanDistSq x (midpoint (B a) (C b))) :=
      Continuous.add (Continuous.pow (continuous_fst.sub continuous_const) 2)
        (Continuous.pow (continuous_snd.sub continuous_const) 2)
    exact measurableSet_le h_cont.measurable measurable_const
  · exact measurableSet_le measurable_const
      (Measurable.sub (measurable_const.mul (measurable_snd.sub measurable_const))
        (measurable_const.mul (measurable_fst.sub measurable_const)))

lemma measurableSet_rightTriangle (a b : ℝ) :
    MeasurableSet (rightTriangle a b) := by
  exact IsCompact.measurableSet ((Set.toFinite _).isCompact_convexHull ℝ)

lemma volume_hSemidisk_lt_top (a : ℝ) : volume (hSemidisk a) < ⊤ := by
  refine' lt_of_le_of_lt (measure_mono (show hSemidisk a ⊆
      Set.Icc (-|a|) (|a|) ×ˢ Set.Icc (-|a|) (|a|) from ?_)) ?_
  · intro x hx
    obtain ⟨h1, h2⟩ := hx
    unfold euclideanDistSq at h1
    unfold LeanEval.Geometry.HippocratesLunes.midpoint at h1; norm_num [A, B] at h1
    constructor <;> constructor <;> cases abs_cases a <;> nlinarith
  · erw [Measure.prod_prod]; norm_num
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

lemma volume_vSemidisk_lt_top (b : ℝ) : volume (vSemidisk b) < ⊤ := by
  refine' lt_of_le_of_lt (measure_mono (show vSemidisk b ⊆
      Set.Icc (-|b|) |b| ×ˢ Set.Icc (-|b|) |b| from ?_)) ?_
  · intro p hp
    simp [vSemidisk] at hp
    obtain ⟨hx, hy⟩ := hp
    unfold LeanEval.Geometry.HippocratesLunes.midpoint at hx; norm_num [A, C, euclideanDistSq] at hx ⊢
    constructor <;> constructor <;> cases abs_cases b <;> nlinarith
  · erw [Measure.prod_prod]; norm_num
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

lemma volume_hypotenuseSemidisk_lt_top (a b : ℝ) :
    volume (hypotenuseSemidisk a b) < ⊤ := by
  refine' lt_of_le_of_lt (measure_mono (show hypotenuseSemidisk a b ⊆
      Metric.closedBall (LeanEval.Geometry.HippocratesLunes.midpoint (B a) (C b))
        (Real.sqrt (euclideanDistSq (B a) (C b) / 4)) from ?_)) ?_
  · intro x hx
    simp_all +decide [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def]
    constructor <;>
      rw [← Real.sqrt_div (by exact add_nonneg (sq_nonneg _) (sq_nonneg _))] <;>
      refine' Real.abs_le_sqrt _
    · exact le_trans (le_add_of_nonneg_right <| sq_nonneg _) hx.1
    · unfold hypotenuseSemidisk at hx; unfold closedHalfDisk at hx
      unfold euclideanDistSq at *; unfold LeanEval.Geometry.HippocratesLunes.midpoint at *
      norm_num at *; nlinarith
  · exact measure_closedBall_lt_top

end Submission.Helpers

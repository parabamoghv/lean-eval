import Submission.Defs
import Submission.Pythagoras
import Submission.Decomp

open LeanEval.Geometry.HippocratesLunes
open MeasureTheory

namespace Submission.Helpers

/-- If `α + β = T + γ + δ` with `γ ≤ α`, `δ ≤ β`, and `α`, `β` finite,
    then `(α - γ) + (β - δ) = T`. -/
lemma ennreal_sub_add {α β γ δ T : ENNReal}
    (hγα : γ ≤ α) (hδβ : δ ≤ β)
    (hα : α ≠ ⊤) (hβ : β ≠ ⊤)
    (hsum : α + β = T + γ + δ) :
    (α - γ) + (β - δ) = T := by
  have h1 : α = γ + (α - γ) := by rw [add_tsub_cancel_of_le hγα]
  have h2 : β = δ + (β - δ) := by rw [add_tsub_cancel_of_le hδβ]
  have h3 : α + β = γ + δ + (α - γ) + (β - δ) := by
    convert congr_arg₂ (· + ·) h1 h2 using 1; ring
  have h4 : T + γ + δ = γ + δ + T := by ring
  have h5 : T = (α - γ) + (β - δ) := by
    rw [← ENNReal.add_right_inj]
    rw [← add_assoc, ← h4, ← hsum, h3]
    exact ne_of_lt (ENNReal.add_lt_top.mpr
      ⟨lt_top_iff_ne_top.mpr (by rintro rfl; simp_all +singlePass),
       lt_top_iff_ne_top.mpr (by rintro rfl; simp_all +singlePass)⟩)
  exact h5.symm

theorem hippocrates_from_lemmas (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b) :
    volume (horizontalLune a b) + volume (verticalLune a b) =
      volume (rightTriangle a b) := by
  unfold horizontalLune verticalLune
  change volume (hSemidisk a \ hypotenuseSemidisk a b) +
    volume (vSemidisk b \ hypotenuseSemidisk a b) =
    volume (rightTriangle a b)
  have hS_a_diff : volume (hSemidisk a \ hypotenuseSemidisk a b) =
      volume (hSemidisk a) - volume (hSemidisk a ∩ hypotenuseSemidisk a b) := by
    rw [Set.diff_self_inter.symm]
    exact measure_diff Set.inter_subset_left
      ((measurableSet_hSemidisk a).inter
        (measurableSet_hypotenuseSemidisk a b)).nullMeasurableSet
      ((measure_mono Set.inter_subset_left).trans_lt (volume_hSemidisk_lt_top a)).ne
  have hS_b_diff : volume (vSemidisk b \ hypotenuseSemidisk a b) =
      volume (vSemidisk b) - volume (vSemidisk b ∩ hypotenuseSemidisk a b) := by
    rw [Set.diff_self_inter.symm]
    exact measure_diff Set.inter_subset_left
      ((measurableSet_vSemidisk b).inter
        (measurableSet_hypotenuseSemidisk a b)).nullMeasurableSet
      ((measure_mono Set.inter_subset_left).trans_lt (volume_vSemidisk_lt_top b)).ne
  rw [hS_a_diff, hS_b_diff]
  exact ennreal_sub_add
    (measure_mono Set.inter_subset_left)
    (measure_mono Set.inter_subset_left)
    (volume_hSemidisk_lt_top a).ne
    (volume_vSemidisk_lt_top b).ne
    (by rw [volume_semicircles_pythagoras a b _ha _hb,
            volume_hypotenuseSemidisk_decomp a b _ha _hb])

end Submission.Helpers

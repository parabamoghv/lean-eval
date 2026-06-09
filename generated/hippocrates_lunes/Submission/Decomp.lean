import Submission.Defs

open LeanEval.Geometry.HippocratesLunes
open MeasureTheory

namespace Submission.Helpers

set_option maxHeartbeats 1600000

lemma volume_hypotenuseSemidisk_decomp (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (hypotenuseSemidisk a b) =
      volume (rightTriangle a b) +
        volume (hSemidisk a ∩ hypotenuseSemidisk a b) +
        volume (vSemidisk b ∩ hypotenuseSemidisk a b) := by
          rw [ ← MeasureTheory.measure_union₀, ← MeasureTheory.measure_union₀ ];
          · refine' congr_arg _ _;
            ext ⟨x, y⟩; simp [hypotenuseSemidisk, rightTriangle, hSemidisk, vSemidisk];
            constructor <;> intro h;
            · by_cases hx : x ≤ 0 <;> by_cases hy : y ≤ 0 <;> simp_all +decide [ closedHalfDisk ];
              · unfold euclideanDistSq det2 vec at *;
                unfold LeanEval.Geometry.HippocratesLunes.midpoint at *; norm_num [ A, B, C ] at *;
                exact Or.inr ⟨ by nlinarith, by nlinarith ⟩;
              · unfold euclideanDistSq at *; unfold det2 at *; unfold vec at *; unfold A B C at *; norm_num at *;
                unfold LeanEval.Geometry.HippocratesLunes.midpoint at *; norm_num at *; exact Or.inr ⟨ by nlinarith, by nlinarith ⟩ ;
              · unfold euclideanDistSq det2 vec B C A at *;
                unfold LeanEval.Geometry.HippocratesLunes.midpoint at * ; norm_num at * ; ring_nf at * ;
                exact Or.inl <| Or.inr ⟨ by nlinarith, by nlinarith ⟩;
              · refine Or.inl <| Or.inl <| ?_;
                -- By definition of convex hull, we need to show that $(x, y)$ can be written as a convex combination of $A$, $B a$, and $C b$.
                have h_convex : ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧ (x, y) = α • A + β • B a + γ • C b := by
                  use 1 - x / a - y / b, x / a, y / b;
                  unfold euclideanDistSq det2 vec B C A at *; norm_num at *; ring_nf at *;
                  field_simp;
                  exact ⟨ by linarith, by linarith, by linarith, trivial, trivial, trivial ⟩;
                rw [ convexHull_eq ];
                obtain ⟨ α, β, γ, hα, hβ, hγ, hsum, h ⟩ := h_convex; use Fin 3, { 0, 1, 2 }, fun i => if i = 0 then α else if i = 1 then β else γ, fun i => if i = 0 then A else if i = 1 then B a else C b; simp_all +decide [ Finset.centerMass ] ;
                norm_num [ ← add_assoc, hsum ];
            · rcases h with ( ( h | h ) | h ) <;> simp_all +decide [ closedHalfDisk ];
              -- By definition of convex hull, we know that $(x, y)$ can be written as a convex combination of $A$, $B$, and $C$.
              obtain ⟨u, v, w, hu, hv, hw, hsum⟩ : ∃ u v w : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ w ∧ u + v + w = 1 ∧ (x, y) = u • A + v • B a + w • C b := by
                rw [ convexHull_insert ] at h;
                · norm_num [ segment_eq_image ] at h;
                  rcases h with ⟨ i, hi, j, hj, h ⟩ ; use 1 - j, j * ( 1 - i ), j * i; simp_all +decide [ Prod.ext_iff ] ; ring;
                  exact ⟨ by nlinarith, by nlinarith, trivial, by linarith, by linarith ⟩;
                · norm_num;
              unfold euclideanDistSq det2 vec; norm_num [ A, B, C, LeanEval.Geometry.HippocratesLunes.midpoint ] at *; ring_nf at *; norm_num at *;
              constructor <;> nlinarith [ mul_nonneg ha.le hb.le, mul_nonneg ha.le hu, mul_nonneg ha.le hv, mul_nonneg ha.le hw, mul_nonneg hb.le hu, mul_nonneg hb.le hv, mul_nonneg hb.le hw ];
          · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.inter ( measurableSet_vSemidisk _ ) ( measurableSet_hypotenuseSemidisk _ _ ) );
          · -- The intersection of the right triangle and the vertical semidisk is a subset of the x-axis, which has measure zero.
            have h_inter_x_axis : rightTriangle a b ∩ vSemidisk b ⊆ {p : Plane | p.1 = 0} := by
              intro p hp
              obtain ⟨hp_triangle, hp_vSemidisk⟩ := hp
              have hp_x_nonneg : 0 ≤ p.1 := by
                have h_convex : ∀ p ∈ convexHull ℝ ({A, B a, C b} : Set Plane), 0 ≤ p.1 := by
                  intro p hp
                  rw [convexHull_insert] at hp
                  generalize_proofs at *; (
                  norm_num [ segment_eq_image ] at hp ⊢
                  generalize_proofs at *; (
                  rcases hp with ⟨ i, ⟨ hi₀, hi₁ ⟩, x, ⟨ hx₀, hx₁ ⟩, rfl ⟩ ; norm_num [ A, B, C ] ; nlinarith [ mul_nonneg hx₀ ha.le ] ;));
                  exact ⟨ _, Set.mem_insert _ _ ⟩
                generalize_proofs at *; (
                exact h_convex p hp_triangle)
              have hp_x_nonpos : p.1 ≤ 0 := by
                have := hp_vSemidisk.2; simp_all +decide [ det2, vec, A, C ] ;
                nlinarith
              exact le_antisymm hp_x_nonpos hp_x_nonneg;
            have h_x_axis_zero : volume {p : Plane | p.1 = 0} = 0 := by
              erw [ show { p : ℝ × ℝ | p.1 = 0 } = ( { 0 } ×ˢ Set.univ ) by ext ; aesop, MeasureTheory.Measure.prod_prod ] ; norm_num;
            refine' MeasureTheory.measure_mono_null _ h_x_axis_zero;
            simp_all +decide [ Set.subset_def ];
            intro x y h₁ h₂ h₃; cases h₁ <;> simp_all +decide [ hSemidisk, vSemidisk ] ;
            · exact h_inter_x_axis x y ‹_› h₂;
            · unfold closedHalfDisk at *; simp_all +decide [ A, B, C ] ;
              unfold euclideanDistSq at *; unfold det2 at *; unfold vec at *; unfold LeanEval.Geometry.HippocratesLunes.midpoint at *; norm_num at *; nlinarith;
          · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.inter ( measurableSet_hSemidisk a ) ( measurableSet_hypotenuseSemidisk a b ) );
          · refine' MeasureTheory.measure_mono_null _ _;
            exact { p : ℝ × ℝ | p.2 = 0 };
            · intro p hp
              obtain ⟨hp_triangle, hp_half_disk⟩ := hp
              simp [rightTriangle, hSemidisk, hypotenuseSemidisk] at hp_triangle hp_half_disk ⊢
              unfold closedHalfDisk at hp_half_disk; simp_all +decide [ A, B, C ] ;
              unfold euclideanDistSq at hp_half_disk; unfold det2 at hp_half_disk; unfold vec at hp_half_disk; simp_all +decide [ LeanEval.Geometry.HippocratesLunes.midpoint ] ;
              rw [ convexHull_insert ] at hp_triangle <;> norm_num at *;
              rcases hp_triangle with ⟨ x, y, hx, hy ⟩ ; rw [ segment_eq_image ] at hx hy; obtain ⟨ u, hu, hu' ⟩ := hx; obtain ⟨ v, hv, hv' ⟩ := hy; simp_all +decide ;
              subst hv';
              nlinarith [ mul_nonneg ha.le hb.le, mul_nonneg ha.le hv.1, mul_nonneg hb.le hv.1 ];
            · erw [ show { p : ℝ × ℝ | p.2 = 0 } = ( Set.univ : Set ℝ ) ×ˢ { 0 } by ext ; aesop, MeasureTheory.Measure.prod_prod ] ; norm_num

end Submission.Helpers
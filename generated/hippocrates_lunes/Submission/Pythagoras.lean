import Submission.Defs

open LeanEval.Geometry.HippocratesLunes
open MeasureTheory

namespace Submission.Helpers

set_option maxHeartbeats 1600000

/-
Volume of the horizontal semicircle equals π a² / 8.
-/
lemma volume_hSemidisk_eq (a : ℝ) (ha : 0 < a) :
    volume (hSemidisk a) = ENNReal.ofReal (Real.pi * a ^ 2 / 8) := by
      -- The volume of the semicircle can be computed using the formula for the area of a semicircle.
      have h_volume : volume (hSemidisk a) = ENNReal.ofReal (∫ x in Set.Icc 0 a, ∫ y in Set.Icc (-Real.sqrt (a^2 / 4 - (x - a / 2)^2)) 0, 1) := by
        rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
        · erw [ MeasureTheory.Measure.prod_apply ];
          · rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
            congr with x ; by_cases hx : 0 ≤ x ∧ x ≤ a <;> simp +decide [ hx ];
            · erw [ show ( Prod.mk x ⁻¹' closedHalfDisk A ( B a ) ( fun t => t ≤ 0 ) ) = Set.Icc ( -Real.sqrt ( a^2 / 4 - ( x - a / 2 ) ^2 ) ) 0 from ?_ ];
              · norm_num;
              · ext y; simp [closedHalfDisk, A, B];
                unfold euclideanDistSq LeanEval.Geometry.HippocratesLunes.midpoint vec det2; norm_num; ring_nf; norm_num [ ha.le ] ;
                constructor <;> intro h <;> constructor <;> nlinarith [ Real.sqrt_nonneg ( x * a - x ^ 2 ), Real.mul_self_sqrt ( by nlinarith : 0 ≤ x * a - x ^ 2 ) ];
            · refine' MeasureTheory.measure_mono_null _ ( MeasureTheory.measure_empty );
              intro y hy; contrapose! hx; simp_all +decide [ hSemidisk, closedHalfDisk ];
              unfold euclideanDistSq LeanEval.Geometry.HippocratesLunes.midpoint A B at hy; norm_num at hy; constructor <;> nlinarith;
          · exact measurableSet_hSemidisk a
        · exact Continuous.integrableOn_Icc ( by continuity );
        · exact Filter.Eventually.of_forall fun x => MeasureTheory.integral_nonneg fun y => by norm_num;
      simp_all +decide [MeasureTheory.integral_Icc_eq_integral_Ioc];
      rw [ ← intervalIntegral.integral_of_le ha.le ] ; rw [ intervalIntegral.integral_comp_sub_right fun x => Real.sqrt ( a ^ 2 / 4 - x ^ 2 ) ] ; norm_num ; ring;
      have := @integral_sqrt_one_sub_sq;
      -- By substitution using $ u = \frac{2x}{a} $, we can transform the integral.
      have h_subst : ∫ x in (-a / 2)..a / 2, Real.sqrt (a^2 / 4 - x^2) = (a / 2) * ∫ x in (-1)..1, Real.sqrt (a^2 / 4 - (a * x / 2)^2) := by
        convert intervalIntegral.integral_comp_div _ _ using 3 <;> ring_nf <;> norm_num [ ha.ne' ];
        rw [ mul_right_comm, mul_inv_cancel₀ ( ne_of_gt ( sq_pos_of_pos ha ) ), one_mul ];
      convert congr_arg ENNReal.ofReal h_subst using 1 <;> ring;
      rw [ show ( fun x => Real.sqrt ( a ^ 2 * ( 1 / 4 ) + a ^ 2 * x ^ 2 * ( -1 / 4 ) ) ) = fun x => a / 2 * Real.sqrt ( 1 - x ^ 2 ) by ext x; rw [ show a ^ 2 * ( 1 / 4 ) + a ^ 2 * x ^ 2 * ( -1 / 4 ) = ( a / 2 ) ^ 2 * ( 1 - x ^ 2 ) by ring ] ; rw [ Real.sqrt_mul ( by positivity ), Real.sqrt_sq ( by positivity ) ] ] ; norm_num [ this ] ; ring;

/-
Volume of the vertical semicircle equals π b² / 8.
-/
lemma volume_vSemidisk_eq (b : ℝ) (hb : 0 < b) :
    volume (vSemidisk b) = ENNReal.ofReal (Real.pi * b ^ 2 / 8) := by
      convert volume_hSemidisk_eq b hb using 1;
      have h_reflect : MeasureTheory.MeasurePreserving (fun p : Plane => (p.2, p.1)) (MeasureTheory.volume) (MeasureTheory.volume) := by
        refine' ⟨ measurable_swap, _ ⟩;
        exact MeasureTheory.Measure.prod_swap ..;
      rw [ ← h_reflect.measure_preimage ];
      · congr with x ; simp +decide [ vSemidisk, hSemidisk, closedHalfDisk ];
        unfold euclideanDistSq LeanEval.Geometry.HippocratesLunes.midpoint vec det2 A B C; norm_num; ring;
        norm_num;
      · exact MeasurableSet.nullMeasurableSet ( measurableSet_vSemidisk b )

/-
Volume of the hypotenuse semicircle equals π (a² + b²) / 8.
-/
lemma volume_hypotenuseSemidisk_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (hypotenuseSemidisk a b) = ENNReal.ofReal (Real.pi * (a ^ 2 + b ^ 2) / 8) := by
      -- Use reflection symmetry to show the two halves have equal area.
      have h_reflection : MeasureTheory.MeasurePreserving (fun p : Plane => (a - p.1, b - p.2)) MeasureTheory.volume MeasureTheory.volume := by
        have h_reflection : MeasureTheory.MeasurePreserving (fun p : ℝ => a - p) MeasureTheory.volume MeasureTheory.volume ∧ MeasureTheory.MeasurePreserving (fun p : ℝ => b - p) MeasureTheory.volume MeasureTheory.volume := by
          constructor <;> refine' ⟨ _, _ ⟩;
          · exact measurable_const.sub measurable_id;
          · ext s hs;
            rw [ Measure.map_apply ] <;> norm_num [ hs ];
            · rw [ show ( fun p => a - p ) ⁻¹' s = ( fun p => -p ) ⁻¹' ( s.preimage fun p => a + p ) by ext; simp +decide [ sub_eq_add_neg ] ];
              simp +zetaDelta at *;
            · exact measurable_const.sub measurable_id;
          · exact measurable_const.sub measurable_id;
          · ext s hs;
            rw [ Measure.map_apply ] <;> norm_num [ hs ];
            · rw [ show ( fun p => b - p ) ⁻¹' s = ( fun p => -p ) ⁻¹' ( s.preimage fun p => b + p ) by ext; simp +decide [ sub_eq_add_neg ] ];
              simp +zetaDelta at *;
            · exact measurable_const.sub measurable_id;
        exact h_reflection.1.prod h_reflection.2;
      -- The volume of the full disk is π(a² + b²)/4.
      have h_full_disk : volume {p : Plane | (p.1 - a / 2) ^ 2 + (p.2 - b / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 4} = ENNReal.ofReal (Real.pi * (a ^ 2 + b ^ 2) / 4) := by
        -- The volume of the disk is given by the area of the disk, which is $\pi r^2$.
        have h_disk_area : ∀ r : ℝ, 0 < r → volume {p : Plane | p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2} = ENNReal.ofReal (Real.pi * r ^ 2) := by
          intro r hr
          have h_disk_area : volume {p : Plane | p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2} = ENNReal.ofReal (∫ x in Set.Icc (-r) r, ∫ y in Set.Icc (-Real.sqrt (r ^ 2 - x ^ 2)) (Real.sqrt (r ^ 2 - x ^ 2)), 1) := by
            erw [ MeasureTheory.Measure.prod_apply ];
            · rw [ MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
              · rw [ ← MeasureTheory.lintegral_indicator ] <;> norm_num [ Set.indicator ];
                congr with x ; by_cases hx : -r ≤ x ∧ x ≤ r <;> simp +decide [ hx ];
                · rw [ show { a : ℝ | x ^ 2 + a ^ 2 ≤ r ^ 2 } = Set.Icc ( -Real.sqrt ( r ^ 2 - x ^ 2 ) ) ( Real.sqrt ( r ^ 2 - x ^ 2 ) ) from ?_ ];
                  · norm_num;
                  · ext y; simp [Set.mem_setOf_eq];
                    exact ⟨ fun h => ⟨ neg_le.mpr <| Real.le_sqrt_of_sq_le <| by nlinarith, Real.le_sqrt_of_sq_le <| by nlinarith ⟩, fun h => by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ r ^ 2 - x ^ 2 by nlinarith ) ] ⟩;
                · exact MeasureTheory.measure_mono_null ( fun y hy => hx ⟨ by nlinarith [ hy.out ], by nlinarith [ hy.out ] ⟩ ) ( MeasureTheory.measure_empty );
              · exact Continuous.integrableOn_Icc ( by continuity );
              · exact Filter.Eventually.of_forall fun x => MeasureTheory.integral_nonneg fun y => by norm_num;
            · exact measurableSet_le ( Continuous.measurable ( by continuity ) ) measurable_const;
          simp_all +decide [MeasureTheory.integral_Icc_eq_integral_Ioc, Real.sqrt_nonneg];
          rw [ ← intervalIntegral.integral_of_le ( by linarith ) ] ; ring;
          have := @integral_sqrt_one_sub_sq;
          -- We can simplify the integral using the fact that $\sqrt{r^2 - x^2} = r \sqrt{1 - (x/r)^2}$.
          have h_simplify : ∫ x in (-r)..r, Real.sqrt (r^2 - x^2) = r * ∫ x in (-1)..1, Real.sqrt (r^2 * (1 - x^2)) := by
            convert intervalIntegral.integral_comp_div _ _ using 3 <;> ring <;> norm_num [ hr.ne' ];
            rw [ mul_right_comm, mul_inv_cancel₀ ( ne_of_gt ( sq_pos_of_pos hr ) ), one_mul ];
          norm_num [ h_simplify, this, hr.le ] ; ring;
          rw [ ENNReal.ofReal_mul ( by positivity ), ENNReal.ofReal_pow ( by positivity ) ];
        convert h_disk_area ( Real.sqrt ( ( a ^ 2 + b ^ 2 ) / 4 ) ) ( by positivity ) using 1 <;> norm_num [ Real.sq_sqrt <| show 0 ≤ ( a ^ 2 + b ^ 2 ) / 4 by positivity ] ; ring;
        · rw [ Real.sq_sqrt ( by positivity ) ] ; rw [ ← MeasureTheory.measure_preimage_add_right volume ( a / 2, b / 2 ) ] ; norm_num ; ring;
          exact congr_arg _ ( congr_arg _ ( by ext; constructor <;> rintro h <;> norm_num at * <;> linarith ) );
        · rw [ div_pow, Real.sq_sqrt <| by positivity ] ; ring;
      -- The volume of the hypotenuse semicircle is half the volume of the full disk.
      have h_half_disk : volume (hypotenuseSemidisk a b) = volume {p : Plane | (p.1 - a / 2) ^ 2 + (p.2 - b / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 4 ∧ b * p.1 + a * p.2 ≤ a * b} := by
        congr with p ; simp +decide [ *, det2, vec, closedHalfDisk, hypotenuseSemidisk ] ; ring;
        unfold euclideanDistSq LeanEval.Geometry.HippocratesLunes.midpoint B C; norm_num ; ring;
        constructor <;> intro h <;> constructor <;> linarith;
      -- The volume of the other half of the disk is equal to the volume of the hypotenuse semicircle.
      have h_other_half : volume {p : Plane | (p.1 - a / 2) ^ 2 + (p.2 - b / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 4 ∧ b * p.1 + a * p.2 ≥ a * b} = volume (hypotenuseSemidisk a b) := by
        rw [ h_half_disk, ← h_reflection.measure_preimage ];
        · congr with p ; norm_num ; ring;
          constructor <;> intro h <;> constructor <;> linarith
        · refine' MeasurableSet.nullMeasurableSet _;
          exact MeasurableSet.inter ( measurableSet_le ( Measurable.add ( measurable_fst.sub measurable_const |> Measurable.pow_const <| 2 ) ( measurable_snd.sub measurable_const |> Measurable.pow_const <| 2 ) ) measurable_const ) ( measurableSet_le measurable_const ( Measurable.add ( measurable_const.mul measurable_fst ) ( measurable_const.mul measurable_snd ) ) );
      -- The volume of the full disk is the sum of the volumes of the two halves.
      have h_full_disk_sum : volume {p : Plane | (p.1 - a / 2) ^ 2 + (p.2 - b / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 4} = volume {p : Plane | (p.1 - a / 2) ^ 2 + (p.2 - b / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 4 ∧ b * p.1 + a * p.2 ≤ a * b} + volume {p : Plane | (p.1 - a / 2) ^ 2 + (p.2 - b / 2) ^ 2 ≤ (a ^ 2 + b ^ 2) / 4 ∧ b * p.1 + a * p.2 ≥ a * b} := by
        rw [ ← MeasureTheory.measure_union₀ ];
        · exact congr_arg _ ( by ext; exact ⟨ fun h => by cases le_total ( b * ‹Plane›.1 + a * ‹Plane›.2 ) ( a * b ) <;> [ left; right ] <;> aesop, fun h => by cases h <;> aesop ⟩ );
        · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.inter ( show MeasurableSet { p : Plane | ( p.1 - a / 2 ) ^ 2 + ( p.2 - b / 2 ) ^ 2 ≤ ( a ^ 2 + b ^ 2 ) / 4 } from by exact measurableSet_le ( by exact Continuous.measurable ( by continuity ) ) ( by exact Continuous.measurable ( by continuity ) ) ) ( show MeasurableSet { p : Plane | b * p.1 + a * p.2 ≥ a * b } from by exact measurableSet_le ( by exact Continuous.measurable ( by continuity ) ) ( by exact Continuous.measurable ( by continuity ) ) ) );
        · refine' MeasureTheory.measure_mono_null _ _;
          exact { p : Plane | b * p.1 + a * p.2 = a * b };
          · exact fun x hx => le_antisymm hx.1.2 hx.2.2;
          · erw [ show { p : ℝ × ℝ | b * p.1 + a * p.2 = a * b } = ( Set.range fun x : ℝ => ( x, ( a * b - b * x ) / a ) ) from ?_, MeasureTheory.Measure.prod_apply ];
            · simp +decide [ Set.preimage ];
            · exact ( by rw [ show ( Set.range fun x : ℝ => ( x, ( a * b - b * x ) / a ) ) = { p : ℝ × ℝ | p.2 = ( a * b - b * p.1 ) / a } by ext ; aesop ] ; exact measurableSet_eq_fun ( measurable_snd ) ( by exact Measurable.div_const ( measurable_const.sub ( measurable_const.mul measurable_fst ) ) _ ) );
            · ext ⟨x, y⟩; simp [Set.mem_range];
              constructor <;> intro h <;> rw [ div_eq_iff ha.ne' ] at * <;> linarith;
      rw [ show ( Real.pi * ( a ^ 2 + b ^ 2 ) / 8 : ℝ ) = ( Real.pi * ( a ^ 2 + b ^ 2 ) / 4 ) / 2 by ring, ENNReal.ofReal_div_of_pos ] <;> norm_num;
      rw [ ← h_full_disk, h_full_disk_sum, h_other_half, h_half_disk ];
      rw [ ENNReal.add_div ] ; norm_num

lemma volume_semicircles_pythagoras (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    volume (hSemidisk a) + volume (vSemidisk b) =
      volume (hypotenuseSemidisk a b) := by
  rw [volume_hSemidisk_eq a ha, volume_vSemidisk_eq b hb,
      volume_hypotenuseSemidisk_eq a b ha hb, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  ring_nf

end Submission.Helpers
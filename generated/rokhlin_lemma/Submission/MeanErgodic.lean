import Mathlib

/-!
# Von Neumann Mean Ergodic Theorem

For a linear isometry `U` on a real Hilbert space `E`, the Cesàro averages
`(1/n) ∑_{k<n} U^k x` converge in norm to the orthogonal projection of `x`
onto the fixed subspace `ker(U - id)`.

## Main results

* `fixedSubspace` : definition of the fixed subspace as `ker(U - id)`
* `fixedSubspace_isClosed` : the fixed subspace is closed
* `adjoint_comp_isometry` : `U† ∘ U = id` for an isometry
* `orthogonal_range_sub_one_eq_fixedSubspace` : `(range(U-1))ᗮ = ker(U-1)` for isometries
* `mean_ergodic_theorem` : the full theorem
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace MeanErgodic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Cesàro average operator: `(1/n) ∑_{k<n} U^k x`. -/
def cesaroAvg (U : E →L[ℝ] E) (n : ℕ) (x : E) : E :=
  (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n, (U ^ k) x)

/-- The fixed subspace of a continuous linear map, `ker(U - id)`. -/
def fixedSubspace (U : E →L[ℝ] E) : Submodule ℝ E :=
  LinearMap.ker (U.toLinearMap - LinearMap.id)

set_option linter.unusedSectionVars false in
theorem mem_fixedSubspace_iff (U : E →L[ℝ] E) (x : E) :
    x ∈ fixedSubspace U ↔ U x = x := by
  simp [fixedSubspace, LinearMap.mem_ker, sub_eq_zero]

set_option linter.unusedSectionVars false in
theorem fixedSubspace_isClosed (U : E →L[ℝ] E) :
    IsClosed (fixedSubspace U : Set E) :=
  (U - ContinuousLinearMap.id ℝ E).isClosed_ker

set_option linter.unusedSectionVars false in
instance fixedSubspace_completeSpace (U : E →L[ℝ] E) :
    CompleteSpace (fixedSubspace U) :=
  (fixedSubspace_isClosed U).completeSpace_coe

set_option linter.unusedSectionVars false in
instance fixedSubspace_hasOrthogonalProjection (U : E →L[ℝ] E) :
    (fixedSubspace U).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- `U† ∘ U = id` for a linear isometry. -/
theorem adjoint_comp_isometry (U : E →ₗᵢ[ℝ] E) :
    ContinuousLinearMap.adjoint U.toContinuousLinearMap ∘L U.toContinuousLinearMap =
    ContinuousLinearMap.id ℝ E := by
  ext x
  apply (InnerProductSpace.toDualMap ℝ E).injective
  ext y
  simp [ContinuousLinearMap.adjoint_inner_left, U.inner_map_map]

/-- For an isometry `U`, `U x = x → U† x = x`. -/
theorem adjoint_fixed_of_fixed (U : E →ₗᵢ[ℝ] E) {x : E} (hx : U x = x) :
    ContinuousLinearMap.adjoint U.toContinuousLinearMap x = x := by
  have h := congr_fun (congr_arg DFunLike.coe (adjoint_comp_isometry U)) x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
  have : U.toContinuousLinearMap x = U x := rfl
  rw [this] at h; rw [hx] at h; exact h

/-- For an isometry `U`, `U† x = x → U x = x`. -/
theorem fixed_of_adjoint_fixed (U : E →ₗᵢ[ℝ] E) {x : E}
    (hx : ContinuousLinearMap.adjoint U.toContinuousLinearMap x = x) :
    U x = x := by
  suffices h : ‖U x - x‖ = 0 by rwa [norm_eq_zero, sub_eq_zero] at h
  have h1 : (‖U x - x‖ : ℝ) ^ 2 = 2 * ‖x‖ ^ 2 - 2 * @inner ℝ E _ (U x) x := by
    rw [norm_sub_sq_real, U.norm_map]; ring
  have h2 : @inner ℝ E _ (U x) x = ‖x‖ ^ 2 := by
    rw [show @inner ℝ E _ (U x) x = @inner ℝ E _ (U.toContinuousLinearMap x) x from rfl]
    rw [← ContinuousLinearMap.adjoint_inner_right U.toContinuousLinearMap x x, hx,
        real_inner_self_eq_norm_sq]
  rw [h2] at h1
  have h3 : (‖U x - x‖ : ℝ) ^ 2 = 0 := by linarith
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3

/-
`(range(U - 1))ᗮ = ker(U - 1)` for an isometry.
-/
theorem orthogonal_range_sub_one_eq_fixedSubspace (U : E →ₗᵢ[ℝ] E) :
    (LinearMap.range (U.toContinuousLinearMap.toLinearMap - LinearMap.id)).orthogonal =
    fixedSubspace U.toContinuousLinearMap := by
  refine' le_antisymm _ _;
  · intro x hx; simp_all +decide [ Submodule.mem_orthogonal', inner_sub_right ] ;
    -- By adjoint_fixed_of_fixed, we have `U x = x`.
    have h_fixed : U x = x := by
      apply fixed_of_adjoint_fixed U;
      refine' ext_inner_right ℝ _ ; simp_all +decide [ ContinuousLinearMap.adjoint_inner_left, sub_eq_zero ] ;
    exact mem_fixedSubspace_iff U.toContinuousLinearMap x |>.2 h_fixed;
  · intro x hx; simp_all +decide [ Submodule.mem_orthogonal ] ;
    simp_all +decide [ inner_sub_left, mem_fixedSubspace_iff ];
    intro y; rw [ sub_eq_zero ] ; have := U.inner_map_map y x; aesop;

/-- `(ker(U-1))ᗮ = closure(range(U-1))`. -/
theorem orthogonal_fixedSubspace_eq_closure_range (U : E →ₗᵢ[ℝ] E) :
    (fixedSubspace U.toContinuousLinearMap).orthogonal =
    (LinearMap.range (U.toContinuousLinearMap.toLinearMap - LinearMap.id)).topologicalClosure := by
  rw [← orthogonal_range_sub_one_eq_fixedSubspace U,
      Submodule.orthogonal_orthogonal_eq_closure]

/-! ### Cesàro averages on the fixed subspace -/

/-
On the fixed subspace, `U^k x = x`.
-/
theorem pow_apply_of_fixed (U : E →L[ℝ] E) {x : E} (hx : x ∈ fixedSubspace U) (k : ℕ) :
    (U ^ k) x = x := by
  induction k <;> simp_all +decide [ pow_succ', mem_fixedSubspace_iff ]

/-
On the fixed subspace, Cesàro averages equal `x`.
-/
theorem cesaroAvg_of_fixed (U : E →L[ℝ] E) {x : E} (hx : x ∈ fixedSubspace U)
    {n : ℕ} (hn : 0 < n) :
    cesaroAvg U n x = x := by
  unfold cesaroAvg;
  simp +decide [ pow_apply_of_fixed U hx ];
  rw [ ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ ( by positivity ) ]

/-! ### Telescoping on `range(U - 1)` -/

/-
Key telescoping identity: `∑_{k<n} U^k (U x - x) = U^n x - x`.
-/
set_option linter.unusedSectionVars false in
theorem sum_pow_apply_sub (U : E →L[ℝ] E) (x : E) (n : ℕ) :
    ∑ k ∈ Finset.range n, (U ^ k) (U x - x) = (U ^ n) x - x := by
  induction' n with n ih;
  · simp +decide;
  · rw [ Finset.sum_range_succ, ih, pow_succ' ];
    simp +decide [ ← pow_succ', sub_eq_add_neg, add_assoc ];
    simp +decide [ add_comm, add_left_comm, pow_succ ]

/-
Norm of `U^k x` equals `‖x‖` for isometry.
-/
set_option linter.unusedSectionVars false in
theorem norm_pow_apply_isometry (U : E →ₗᵢ[ℝ] E) (x : E) (k : ℕ) :
    ‖(U.toContinuousLinearMap ^ k) x‖ = ‖x‖ := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply,
      show ‖U.toContinuousLinearMap ((U.toContinuousLinearMap ^ n) x)‖ =
        ‖(U.toContinuousLinearMap ^ n) x‖ from U.norm_map _, ih]

/-
Cesàro averages converge to 0 on elements of the form `(U-1)x`, for isometry `U`.
-/
theorem norm_cesaroAvg_sub_one_le (U : E →ₗᵢ[ℝ] E) (x : E) (n : ℕ) (hn : 0 < n) :
    ‖cesaroAvg U.toContinuousLinearMap n (U x - x)‖ ≤ 2 * ‖x‖ / n := by
  convert norm_smul_le ( ( n : ℝ ) ⁻¹ ) ( ∑ k ∈ Finset.range n, ( ( U.toContinuousLinearMap ^ k ) ( U x - x ) ) ) |> le_trans <| ?_ using 1;
  rw [ le_div_iff₀' ];
  · convert norm_sub_le ( ( U.toContinuousLinearMap ^ n ) x ) x using 1;
    · rw [ ← sum_pow_apply_sub ];
      simp +decide [ hn.ne' ];
    · rw [ two_mul, norm_pow_apply_isometry ];
  · positivity

/-! ### Extending from `range(U-1)` to its closure -/

/-
Cesàro averages are uniformly bounded (norm ≤ ‖x‖) for an isometry.
-/
theorem norm_cesaroAvg_le (U : E →ₗᵢ[ℝ] E) (x : E) (n : ℕ) (hn : 0 < n) :
    ‖cesaroAvg U.toContinuousLinearMap n x‖ ≤ ‖x‖ := by
  unfold cesaroAvg
  refine le_trans (norm_smul_le _ _) ?_
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ)⁻¹))]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)) ?_
  simp only [norm_pow_apply_isometry, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (n : ℝ) ≠ 0), one_mul]

/-
Cesàro averages converge to 0 on the orthogonal complement of the fixed subspace.
-/
theorem cesaroAvg_tendsto_zero_on_orthogonal (U : E →ₗᵢ[ℝ] E) {x : E}
    (hx : x ∈ (fixedSubspace U.toContinuousLinearMap).orthogonal) :
    Filter.Tendsto (fun n => cesaroAvg U.toContinuousLinearMap n x) Filter.atTop (nhds 0) := by
  -- By orthogonal_fixedSubspace_eq_closure_range, x is in the closure of range(U-1).
  have hx_closure : x ∈ (LinearMap.range (U.toContinuousLinearMap.toLinearMap - LinearMap.id)).topologicalClosure := by
    have := orthogonal_fixedSubspace_eq_closure_range U;
    exact this ▸ hx;
  -- For ε > 0, find y in range(U-1) with ‖x - y‖ < ε/2. Write y = (U-1)z for some z.
  have h_eps : ∀ ε > 0, ∃ y ∈ LinearMap.range (U.toContinuousLinearMap.toLinearMap - LinearMap.id), ‖x - y‖ < ε := by
    exact fun ε εpos => by rcases Metric.mem_closure_iff.1 hx_closure ε εpos with ⟨ y, hy, hy' ⟩ ; exact ⟨ y, hy, by simpa [ dist_eq_norm ] using hy' ⟩ ;
  generalize_proofs at *;
  -- Then cesaroAvg n x = cesaroAvg n (x-y) + cesaroAvg n y.
  have h_split : ∀ y ∈ LinearMap.range (U.toContinuousLinearMap.toLinearMap - LinearMap.id), ∀ n > 0, cesaroAvg U.toContinuousLinearMap n x = cesaroAvg U.toContinuousLinearMap n (x - y) + cesaroAvg U.toContinuousLinearMap n y := by
    intro y hy n hn
    simp [cesaroAvg];
    rw [ ← smul_add, sub_add_cancel ]
  generalize_proofs at *;
  -- By norm_cesaroAvg_le, ‖cesaroAvg n (x-y)‖ ≤ ‖x-y‖ < ε/2.
  have h_bound1 : ∀ ε > 0, ∃ y ∈ LinearMap.range (U.toContinuousLinearMap.toLinearMap - LinearMap.id), ∀ n > 0, ‖cesaroAvg U.toContinuousLinearMap n (x - y)‖ < ε / 2 := by
    exact fun ε εpos => by rcases h_eps ( ε / 2 ) ( half_pos εpos ) with ⟨ y, hy, hy' ⟩ ; exact ⟨ y, hy, fun n hn => lt_of_le_of_lt ( norm_cesaroAvg_le U ( x - y ) n hn ) hy' ⟩ ;
  generalize_proofs at *;
  -- By norm_cesaroAvg_sub_one_le, ‖cesaroAvg n y‖ ≤ 2‖z‖/n → 0.
  have h_bound2 : ∀ y ∈ LinearMap.range (U.toContinuousLinearMap.toLinearMap - LinearMap.id), Filter.Tendsto (fun n => ‖cesaroAvg U.toContinuousLinearMap n y‖) Filter.atTop (nhds 0) := by
    intro y hy
    obtain ⟨z, hz⟩ : ∃ z, y = U.toContinuousLinearMap z - z := by
      exact hy.imp fun z hz => hz.symm
    generalize_proofs at *;
    exact squeeze_zero_norm' ( Filter.eventually_atTop.mpr ⟨ 1, fun n hn => by simpa [ hz ] using norm_cesaroAvg_sub_one_le U z n hn ⟩ ) ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop )
  generalize_proofs at *;
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε; rcases h_bound1 ε hε with ⟨ y, hy, hy' ⟩ ; filter_upwards [ Filter.eventually_gt_atTop 0, h_bound2 y hy |> fun h => h.eventually ( gt_mem_nhds <| half_pos hε ) ] with n hn hn' using by simpa [ h_split y hy n hn ] using lt_of_le_of_lt ( norm_add_le _ _ ) ( by linarith [ hy' n hn ] ) ;

/-! ### Main theorem -/

/-
**Von Neumann Mean Ergodic Theorem**: For a linear isometry `U` on a Hilbert space,
the Cesàro averages `(1/n) ∑_{k<n} U^k x` converge to the orthogonal projection
of `x` onto the fixed subspace `ker(U - id)`.
-/
theorem mean_ergodic_theorem (U : E →ₗᵢ[ℝ] E) (x : E) :
    Filter.Tendsto (fun n => cesaroAvg U.toContinuousLinearMap n x) Filter.atTop
      (nhds ((fixedSubspace U.toContinuousLinearMap).orthogonalProjection x : E)) := by
  -- Write x as the sum of its projection onto the fixed subspace and its projection onto the orthogonal complement.
  set Px := (fixedSubspace U.toContinuousLinearMap).orthogonalProjection x with hPx;
  -- By linearity of the Cesàro average, we can split the limit into the sum of the limits.
  have h_split : Filter.Tendsto (fun n => cesaroAvg U.toContinuousLinearMap n Px + cesaroAvg U.toContinuousLinearMap n (x - Px)) Filter.atTop (nhds (Px + 0)) := by
    refine' Filter.Tendsto.add _ _;
    · exact tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ cesaroAvg_of_fixed _ ( Submodule.coe_mem _ ) hn ] );
    · convert cesaroAvg_tendsto_zero_on_orthogonal U _;
      simp +zetaDelta at *;
  simp_all +decide [ ← smul_add, cesaroAvg ]

end MeanErgodic

end
/-
  Proof that centralizer(symAction) ≤ adjoin(glAction).
-/
import ChallengeDeps
import Submission.TensorPowHelpers
import Submission.Polarization

set_option maxHeartbeats 800000

namespace Submission.CentralizerContainment

open scoped TensorProduct
open LeanEval.RepresentationTheory

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
variable {k : ℕ}

lemma isUnit_id_add_smul_of_nilpotent {f : M →ₗ[R] M} (hf : IsNilpotent f) (t : R) :
    IsUnit (LinearMap.id + t • f) := by
  rw [show LinearMap.id + t • f = t • f + LinearMap.id from by abel]
  exact (hf.smul t).isUnit_add_one

lemma nilpotent_shifted_in_adjoin {f : M →ₗ[R] M} (hf : IsNilpotent f) (t : R) :
    PiTensorProduct.map (fun _ : Fin k => (LinearMap.id + t • f)) ∈
      Algebra.adjoin R (Set.range (glAction R M k)) := by
  have hu := isUnit_id_add_smul_of_nilpotent hf t
  have key : PiTensorProduct.map (fun _ : Fin k => (LinearMap.id + t • f)) =
    glAction R M k hu.unit := by simp [glAction]
  rw [key]; exact Algebra.subset_adjoin ⟨hu.unit, rfl⟩

lemma finrank_ker_lt_of_perturbation (f : M →ₗ[R] M) (v : M) (φ : M →ₗ[R] R)
    (hv_not_range : v ∉ LinearMap.range f)
    (w : M) (hw_ker : f w = 0) (hφw : φ w ≠ 0) (hφv : φ v = 0)
    (c : R) (hc : c ≠ 0) :
    Module.finrank R (LinearMap.ker (f + c • φ.smulRight v)) <
      Module.finrank R (LinearMap.ker f) := by
  by_cases h : LinearMap.range ( f + c • φ.smulRight v ) = LinearMap.range f <;> simp_all +decide [ Submodule.eq_top_iff' ]
  · replace h := SetLike.ext_iff.mp h ( v ) ; simp_all +decide [ LinearMap.mem_range ]
    contrapose! h
    refine' ⟨ ( c⁻¹ * ( φ w ) ⁻¹ ) • w, _ ⟩ ; simp +decide [ *, mul_assoc, smul_smul ]
  · have h_rank : Module.finrank R (LinearMap.range (f + c • φ.smulRight v)) > Module.finrank R (LinearMap.range f) := by
      refine' Submodule.finrank_lt_finrank_of_lt ( lt_of_le_of_ne _ _ )
      · intro x hx
        obtain ⟨ y, rfl ⟩ := hx
        refine' ⟨ y - ( φ y / φ w ) • w, _ ⟩ ; simp +decide [ hw_ker, hφw, hφv, hc, smul_smul ]
      · exact Ne.symm h
    have := LinearMap.finrank_range_add_finrank_ker ( f + c • φ.smulRight v )
    have := LinearMap.finrank_range_add_finrank_ker f
    simp_all +decide [ add_comm ] ; linarith

/-- Helper: for 0 < j ≤ k with k! invertible, (j : R) ≠ 0. -/
private lemma nat_cast_ne_zero_of_dvd_factorial (j : ℕ) (hj : 0 < j) (hjk : j ≤ k)
    [Invertible (k.factorial : R)] : (j : R) ≠ 0 := by
  intro h
  have hd : (j : ℕ) ∣ k.factorial := Nat.dvd_factorial hj hjk
  obtain ⟨c, hc⟩ := hd
  have : (k.factorial : R) = 0 := by rw [hc, Nat.cast_mul, h, zero_mul]
  exact not_isUnit_zero (this ▸ isUnit_of_invertible (k.factorial : R))

/-
For any f, f^⊗k ∈ adjoin(glAction).
-/
theorem tensorPow_in_adjoin [Invertible (k.factorial : R)]
    (f : M →ₗ[R] M) :
    PiTensorProduct.map (fun _ : Fin k => f) ∈
      Algebra.adjoin R (Set.range (glAction R M k)) := by
  -- Strong induction on finrank of ker(f)
  induction h : Module.finrank R (LinearMap.ker f) using Nat.strongRecOn generalizing f with
  | _ n ih =>
  by_cases hf_surj : Function.Surjective f
  · have hf_unit : IsUnit f := (Module.End.isUnit_iff f).mpr
      ⟨LinearMap.injective_iff_surjective.mpr hf_surj, hf_surj⟩
    exact Algebra.subset_adjoin ⟨hf_unit.unit, rfl⟩
  · -- f not surjective: use finite difference + induction
    by_cases hf_zero : f = 0
    · -- f = 0: f^⊗k = 0 (for k ≥ 1) or id (for k = 0), both in adjoin
      subst hf_zero
      by_cases hk : k = 0
      · subst hk
        have : PiTensorProduct.map (fun _ : Fin 0 => (0 : M →ₗ[R] M)) =
            (1 : Module.End R (⨂[R]^0 M)) := by
          ext; simp [PiTensorProduct.map];
          convert rfl
        rw [this]; exact Subalgebra.one_mem _
      · have : PiTensorProduct.map (fun _ : Fin k => (0 : M →ₗ[R] M)) = 0 := by
          ext x; simp [PiTensorProduct.map_tprod]
          have ⟨i⟩ := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)
          exact MultilinearMap.map_coord_zero _ i rfl
        rw [this]; exact Subalgebra.zero_mem _
    · -- f ≠ 0, not surjective
      -- range f and ker f are both proper submodules
      have hrange_ne_top : (LinearMap.range f : Submodule R M) ≠ ⊤ := by
        intro h; exact hf_surj (LinearMap.range_eq_top.mp h)
      have hker_ne_top : (LinearMap.ker f : Submodule R M) ≠ ⊤ := by
        intro h; exact hf_zero (LinearMap.ker_eq_top.mp h)
      -- Choose v ∉ range f ∪ ker f (possible since union of two proper submodules is proper)
      obtain ⟨v, hv_range, hv_ker⟩ := Polarization.union_proper_submodules
        (LinearMap.range f) (LinearMap.ker f) hrange_ne_top hker_ne_top
      have hv_ne : v ≠ 0 := fun h => hv_range (h ▸ (LinearMap.range f).zero_mem)
      -- Choose w ∈ ker f, w ≠ 0
      have hker_ne_bot : LinearMap.ker f ≠ ⊥ := by
        intro hbot; exact hf_surj ((LinearMap.injective_iff_surjective).mp (LinearMap.ker_eq_bot.mp hbot))
      obtain ⟨w, hw_ker, hw_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne_bot
      -- w ∉ span{v} because v ∉ ker f but w ∈ ker f
      have hw_not_span_v : w ∉ Submodule.span R {v} := by
        intro h_in
        rw [Submodule.mem_span_singleton] at h_in
        obtain ⟨c, rfl⟩ := h_in
        have hc_ne : c ≠ 0 := fun hc => hw_ne (by simp [hc])
        have hfv : f (c • v) = 0 := LinearMap.mem_ker.mp hw_ker
        simp [hc_ne] at hfv
        exact hv_ker (LinearMap.mem_ker.mpr hfv)
      -- Find separating functional φ with φ(v) = 0, φ(w) ≠ 0
      obtain ⟨φ, hφv, hφw⟩ : ∃ φ : M →ₗ[R] R, φ v = 0 ∧ φ w ≠ 0 := by
        have h_dual : ∃ φ : M →ₗ[R] R, φ w ≠ 0 ∧ ∀ x ∈ Submodule.span R {v}, φ x = 0 := by
          exact Submodule.exists_le_ker_of_notMem hw_not_span_v;
        exact ⟨ h_dual.choose, h_dual.choose_spec.2 v ( Submodule.mem_span_singleton_self v ), h_dual.choose_spec.1 ⟩
      -- Define E = φ.smulRight v
      set E : M →ₗ[R] M := φ.smulRight v with hE_def
      have hE_nil : IsNilpotent E := ⟨2, by show E * E = 0; ext m; simp [hE_def, LinearMap.smulRight_apply, hφv]⟩
      -- For 0 < j ≤ k: finrank(ker(f + j•E)) < n
      have hfr_lt : ∀ j : ℕ, 0 < j → j ≤ k →
          Module.finrank R (LinearMap.ker (f + (j : R) • E)) < n := by
        intro j hj hjk
        rw [← h]
        exact finrank_ker_lt_of_perturbation f v φ hv_range
          w (LinearMap.mem_ker.mp hw_ker) hφw hφv (j : R)
          (nat_cast_ne_zero_of_dvd_factorial j hj hjk)
      -- Extract f^⊗k from the finite difference identity
      have hdiff := Submission.TensorPowHelpers.finite_diff_tensorPow (R := R) (M := M) (k := k) f E
      have hE_in := Submission.TensorPowHelpers.nilpotent_tensorPow_in_adjoin (R := R) (M := M) (k := k) hE_nil
      set A := Algebra.adjoin R (Set.range (glAction R M k))
      have hsplit : ∑ j ∈ Finset.range (k + 1),
          ((-1 : R) ^ (k - j) * (k.choose j : R)) •
            PiTensorProduct.map (fun _ : Fin k => f + (j : R) • E) =
          ((-1 : R) ^ k • PiTensorProduct.map (fun _ : Fin k => f)) +
          ∑ j ∈ Finset.Ico 1 (k + 1),
            ((-1 : R) ^ (k - j) * (k.choose j : R)) •
              PiTensorProduct.map (fun _ : Fin k => f + (j : R) • E) := by
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
        simp
      have htail_in : ∑ j ∈ Finset.Ico 1 (k + 1),
          ((-1 : R) ^ (k - j) * (k.choose j : R)) •
            PiTensorProduct.map (fun _ : Fin k => f + (j : R) • E) ∈ A := by
        apply Subalgebra.sum_mem
        intro j hj
        apply Subalgebra.smul_mem
        have hj_mem := Finset.mem_Ico.mp hj
        exact ih _ (hfr_lt j (by omega) (by omega)) _ rfl
      have hneg1k_smul_in : (-1 : R) ^ k • PiTensorProduct.map (fun _ : Fin k => f) ∈ A := by
        have : (-1 : R) ^ k • PiTensorProduct.map (fun _ : Fin k => f) =
            (k.factorial : R) • PiTensorProduct.map (fun _ : Fin k => E) -
            ∑ j ∈ Finset.Ico 1 (k + 1),
              ((-1 : R) ^ (k - j) * (k.choose j : R)) •
                PiTensorProduct.map (fun _ : Fin k => f + (j : R) • E) := by
          have := hdiff; rw [hsplit] at this
          exact eq_sub_of_add_eq this
        rw [this]
        exact A.sub_mem (A.smul_mem hE_in _) htail_in
      have : PiTensorProduct.map (fun _ : Fin k => f) =
          (-1 : R) ^ k • ((-1 : R) ^ k • PiTensorProduct.map (fun _ : Fin k => f)) := by
        rw [smul_smul]; simp [← pow_add, ← two_mul, pow_mul]
      rw [this]; exact A.smul_mem hneg1k_smul_in _

/-- The centralizer of S_k is contained in adjoin of tensor powers.
    Proved in Submission.Polarization using pure tensor spanning + polarization identity. -/
theorem centralizer_le_adjoin_tensorPow [Invertible (k.factorial : R)] :
    Subalgebra.centralizer R (Set.range (symAction R M k)) ≤
      Algebra.adjoin R (Set.range (fun f : M →ₗ[R] M =>
        PiTensorProduct.map (fun _ : Fin k => f))) :=
  Polarization.centralizer_le_adjoin_tensorPow

/-- The main theorem: centralizer(symAction) ≤ adjoin(glAction). -/
theorem main [Invertible (k.factorial : R)] :
    Subalgebra.centralizer R (Set.range (symAction R M k)) ≤
      Algebra.adjoin R (Set.range (glAction R M k)) := by
  calc Subalgebra.centralizer R (Set.range (symAction R M k))
    _ ≤ Algebra.adjoin R (Set.range (fun f : M →ₗ[R] M =>
          PiTensorProduct.map (fun _ : Fin k => f))) := centralizer_le_adjoin_tensorPow
    _ ≤ Algebra.adjoin R (Set.range (glAction R M k)) := by
        apply Algebra.adjoin_le; rintro x ⟨f, rfl⟩; exact tensorPow_in_adjoin f

end Submission.CentralizerContainment

import ChallengeDeps
import Submission.DCT

namespace LeanEval.RepresentationTheory
open scoped TensorProduct

/-- Each symAction σ commutes with each glAction g. -/
lemma symAction_comm_glAction {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {k : ℕ} (σ : Equiv.Perm (Fin k)) (g : (M →ₗ[R] M)ˣ) :
    symAction R M k σ * glAction R M k g = glAction R M k g * symAction R M k σ := by
  ext x;
  simp +decide [ symAction, glAction, PiTensorProduct.map_tprod, PiTensorProduct.reindex_tprod ]

/-- Forward inclusion: adjoin(range(sym)) ≤ centralizer(range(gl)). -/
lemma adjoin_symAction_le_centralizer_glAction {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    {k : ℕ} :
    Algebra.adjoin R (Set.range (symAction R M k)) ≤
      Subalgebra.centralizer R (Set.range (glAction R M k)) := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨σ, rfl⟩
  intro g hg
  simp at *
  rcases hg with ⟨y, rfl⟩
  exact symAction_comm_glAction σ y ▸ rfl

/-- Centralizer of the coe of an adjoin equals centralizer of the set. -/
lemma Subalgebra.centralizer_adjoin_eq {R : Type*} [CommSemiring R]
    {A : Type*} [Semiring A] [Algebra R A] (s : Set A) :
    Subalgebra.centralizer R (↑(Algebra.adjoin R s) : Set A) = Subalgebra.centralizer R s := by
  apply le_antisymm
  · exact Subalgebra.centralizer_le R _ _ Algebra.subset_adjoin
  · intro x hx
    rw [Subalgebra.mem_centralizer_iff] at hx ⊢
    intro y hy
    have hy' := (Algebra.adjoin_le_centralizer_centralizer R s) hy
    rw [Subalgebra.mem_centralizer_iff] at hy'
    exact (hy' x (by simp [Subalgebra.coe_centralizer, Set.mem_centralizer_iff]; exact hx)).symm

/-- Backward inclusion: centralizer(range(gl)) ≤ adjoin(range(sym)).
This is the hard direction of Schur-Weyl duality. -/
lemma centralizer_glAction_le_adjoin_symAction {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
    {k : ℕ} [Invertible (k.factorial : R)] :
    Subalgebra.centralizer R (Set.range (glAction R M k)) ≤
      Algebra.adjoin R (Set.range (symAction R M k)) := by
  -- Let A = adjoin(range(sym)), C_A = centralizer(↑A), adjoin_gl = adjoin(range(gl))
  set A := Algebra.adjoin R (Set.range (symAction R M k))
  set C_A := Subalgebra.centralizer R (↑A : Set (Module.End R (⨂[R]^k M)))
  set adjoin_gl := Algebra.adjoin R (Set.range (glAction R M k))
  -- Step 1: C(range(sym)) ≤ adjoin(range(gl))
  have h_cent_cont := @Submission.centralizer_symAction_le_adjoin_glAction R _ M _ _ _ k _
  -- Step 2: C_A = C(range(sym))
  have h_cent_adjoin : C_A =
      Subalgebra.centralizer R (Set.range (symAction R M k)) :=
    Subalgebra.centralizer_adjoin_eq _
  -- Step 3: C_A ≤ adjoin_gl
  have h3 : C_A ≤ adjoin_gl := h_cent_adjoin ▸ h_cent_cont
  -- Step 4: C(↑adjoin_gl) ≤ C(↑C_A)
  have h4 : Subalgebra.centralizer R (SetLike.coe adjoin_gl) ≤
      Subalgebra.centralizer R (SetLike.coe C_A) := by
    intro x hx
    rw [Subalgebra.mem_centralizer_iff] at hx ⊢
    intro g hg
    exact hx g (SetLike.coe_subset_coe.mpr h3 hg)
  -- Step 5: C(↑adjoin_gl) = C(range(gl))
  have h5 : Subalgebra.centralizer R (SetLike.coe adjoin_gl) =
      Subalgebra.centralizer R (Set.range (glAction R M k)) :=
    Subalgebra.centralizer_adjoin_eq _
  -- Step 6: C(↑C_A) = A by DCT
  have h6 : Subalgebra.centralizer R (SetLike.coe C_A) = A :=
    Submission.Subalgebra.centralizer_centralizer_eq_of_isSemisimpleModule A
      (Submission.tensorPower_isSemisimpleModule_adjoin_symAction)
  -- Combine: C(range(gl)) ≤ A
  calc Subalgebra.centralizer R (Set.range (glAction R M k))
      _ = Subalgebra.centralizer R (SetLike.coe adjoin_gl) := h5.symm
      _ ≤ Subalgebra.centralizer R (SetLike.coe C_A) := h4
      _ = A := h6

end LeanEval.RepresentationTheory

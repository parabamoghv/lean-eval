/-
  Supporting lemmas for the backward direction of Schur-Weyl duality.
-/
import ChallengeDeps
import Submission.DCTProof
import Submission.CentralizerContainment

namespace Submission

open scoped TensorProduct
open LeanEval.RepresentationTheory

section FiniteDimensionalTensorPower

variable {R : Type*} [CommSemiring R]
variable {M : Type*} [AddCommMonoid M] [Module R M]

/-- Auxiliary equivalence: ⨂[R]^(n+1) M ≃ₗ[R] (⨂[R]^n M) ⊗[R] M -/
noncomputable def tensorPowerSuccEquiv (n : ℕ) :
    (⨂[R]^(n+1) M) ≃ₗ[R] (⨂[R]^n M) ⊗[R] M := by
  have e1 : (⨂[R]^(n+1) M) ≃ₗ[R] ⨂[R] (x : Fin n ⊕ Fin 1), M :=
    PiTensorProduct.reindex R _ finSumFinEquiv.symm
  have e2 : (⨂[R] (x : Fin n ⊕ Fin 1), M) ≃ₗ[R] (⨂[R]^n M) ⊗[R] (⨂[R]^1 M) :=
    (PiTensorProduct.tmulEquiv R M).symm
  have e3 : (⨂[R]^1 M) ≃ₗ[R] M :=
    PiTensorProduct.subsingletonEquiv 0
  exact e1.trans (e2.trans (TensorProduct.congr (LinearEquiv.refl R _) e3))

/-- The tensor power of a finitely generated module is finitely generated. -/
instance tensorPower_finite [Module.Finite R M] (k : ℕ) :
    Module.Finite R (⨂[R]^k M) := by
  induction k with
  | zero =>
    have : (⨂[R]^0 M) ≃ₗ[R] R := PiTensorProduct.isEmptyEquiv (Fin 0)
    exact Module.Finite.equiv this.symm
  | succ n ih =>
    exact Module.Finite.equiv (tensorPowerSuccEquiv n).symm

end FiniteDimensionalTensorPower

/-- The tensor power of a finite-dimensional space is finite-dimensional. -/
instance tensorPower_finiteDimensional {R : Type*} [Field R]
    {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M] (k : ℕ) :
    FiniteDimensional R (⨂[R]^k M) :=
  tensorPower_finite k

section Maschke

variable {R : Type*} [Field R]

/-- The symmetric group algebra R[S_k] is semisimple when k! is invertible. -/
instance monoidAlgebra_isSemisimpleRing (k : ℕ) [Invertible (k.factorial : R)] :
    IsSemisimpleRing (MonoidAlgebra R (Equiv.Perm (Fin k))) := by
  have h_card_inv : Invertible (Nat.card (Equiv.Perm (Fin k)) : R) := by
    convert ‹Invertible (k.factorial : R)› using 1
    simp +decide [Fintype.card_perm]
  exact MonoidAlgebra.Submodule.instIsSemisimpleModule

end Maschke

section DCT

variable {R : Type*} [Field R]
variable {V : Type*} [AddCommGroup V] [Module R V] [FiniteDimensional R V]

/-- Double Centralizer Theorem for semisimple subalgebras:
If A is a subalgebra of End_R(V) such that V is semisimple as an A-module,
then the double centralizer of A equals A. -/
theorem Subalgebra.centralizer_centralizer_eq_of_isSemisimpleModule
    (A : Subalgebra R (Module.End R V))
    (hss : @IsSemisimpleModule A _ V _ (Module.compHom V A.val.toRingHom)) :
    Subalgebra.centralizer R ↑(Subalgebra.centralizer R (↑A : Set (Module.End R V))) = A :=
  Submission.DCTProof.centralizer_centralizer_eq A hss

end DCT

section Semisimplicity

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
variable {k : ℕ} [Invertible (k.factorial : R)]

/-
V^⊗k is semisimple as a module over adjoin(range(symAction)).
This follows from Maschke's theorem: R[S_k] is semisimple, the action factors
through adjoin(range(sym)), and modules over (quotients of) semisimple rings
are semisimple.
-/
theorem tensorPower_isSemisimpleModule_adjoin_symAction :
    let A := Algebra.adjoin R (Set.range (symAction R M k))
    @IsSemisimpleModule A _ (⨂[R]^k M) _ (Module.compHom (⨂[R]^k M) A.val.toRingHom) := by
  -- The symmetric group $S_k$ acts on $V^{\otimes k}$ by permuting the tensor factors.
  set A := Algebra.adjoin R (Set.range (symAction R M k));
  -- The action of $S_k$ on $V^{\otimes k}$ factors through the algebra homomorphism $\phi : R[S_k] \to \text{End}(V^{\otimes k})$.
  obtain ⟨ϕ, hϕ⟩ : ∃ ϕ : MonoidAlgebra R (Equiv.Perm (Fin k)) →ₐ[R] Module.End R (⨂[R]^k M), ∀ σ : Equiv.Perm (Fin k), ϕ (MonoidAlgebra.of R (Equiv.Perm (Fin k)) σ) = symAction R M k σ := by
    refine' ⟨ _, _ ⟩;
    refine' MonoidAlgebra.lift _ _ _ _;
    exact symAction R M k;
    aesop;
  -- Since $R[S_k]$ is semisimple, the image of $\phi$ is also semisimple.
  have h_image_semisimple : IsSemisimpleRing (↥(ϕ.range)) := by
    have h_image_semisimple : IsSemisimpleRing (MonoidAlgebra R (Equiv.Perm (Fin k))) := by
      exact monoidAlgebra_isSemisimpleRing k;
    convert h_image_semisimple;
    constructor <;> intro h;
    · exact h_image_semisimple;
    · have h_image_semisimple : IsSemisimpleRing (↥(ϕ.range)) := by
        have h_surjective : Function.Surjective (ϕ.rangeRestrict) := by
          exact fun x => by rcases x with ⟨ x, hx ⟩ ; exact ⟨ Classical.choose hx, Subtype.ext <| Classical.choose_spec hx ⟩ ;
        exact RingHom.isSemisimpleRing_of_surjective ϕ.rangeRestrict.toRingHom h_surjective;
      exact h_image_semisimple;
  have h_image_eq_A : ϕ.range = A := by
    refine' le_antisymm _ _;
    · rintro _ ⟨ x, rfl ⟩;
      induction x using MonoidAlgebra.induction_on <;> aesop;
    · exact Algebra.adjoin_le fun x hx => by obtain ⟨ σ, rfl ⟩ := hx; exact ⟨ _, hϕ σ ⟩ ;
  rw [ ← h_image_eq_A ];
  convert h_image_semisimple.isSemisimpleModule

end Semisimplicity

section CentralizerContainment

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]

/-- The centralizer of the S_k algebra in End(V^⊗k) is contained in
the algebra generated by the GL action. -/
theorem centralizer_symAction_le_adjoin_glAction
    {k : ℕ} [Invertible (k.factorial : R)] :
    Subalgebra.centralizer R (Set.range (symAction R M k)) ≤
      Algebra.adjoin R (Set.range (glAction R M k)) :=
  CentralizerContainment.main

end CentralizerContainment

end Submission

/-
  Proof of the Double Centralizer Theorem via helper lemmas.
-/
import ChallengeDeps

namespace Submission.DCTProof

open scoped TensorProduct

variable {R : Type*} [Field R]
variable {V : Type*} [AddCommGroup V] [Module R V] [FiniteDimensional R V]
variable (A : Subalgebra R (Module.End R V))

/-- The diagonal linear action of f ∈ End(V) on Fin n → V. -/
def diagMap {n : ℕ} (f : Module.End R V) : Module.End R (Fin n → V) :=
  LinearMap.pi (fun i => f.comp (LinearMap.proj i))

@[simp] lemma diagMap_apply {n : ℕ} (f : Module.End R V) (w : Fin n → V) (i : Fin n) :
    diagMap f w i = f (w i) := by
  simp [diagMap]

/-- Matrix entry of an endomorphism: φᵢⱼ(v) = (φ (Pi.single j v)) i. -/
noncomputable def matrixEntry {n : ℕ} (φ : Module.End R (Fin n → V)) (i j : Fin n) :
    Module.End R V :=
  (LinearMap.proj i).comp (φ.comp (LinearMap.single R (fun _ : Fin n => V) j))

/-
φ(w)(i) = Σⱼ matrixEntry φ i j (w j).
-/
lemma apply_eq_sum_matrixEntry {n : ℕ} (φ : Module.End R (Fin n → V))
    (w : Fin n → V) (i : Fin n) :
    φ w i = ∑ j : Fin n, matrixEntry φ i j (w j) := by
  convert congr_arg ( fun x => φ x i ) ( show w = ∑ j, Pi.single j ( w j ) from ?_ );
  · induction' ( Finset.univ : Finset ( Fin n ) ) using Finset.induction <;> aesop;
  · ext j; simp +decide [ Pi.single_apply ]

/-
Matrix entry commutes with a.val when φ commutes with diagMap a.val for all a ∈ A.
-/
lemma matrixEntry_comm_A {n : ℕ} (φ : Module.End R (Fin n → V))
    (hφ : ∀ (a : A), diagMap (n := n) a.val ∘ₗ φ = φ ∘ₗ diagMap a.val)
    (i j : Fin n) (a : A) :
    matrixEntry φ i j * a.val = a.val * matrixEntry φ i j := by
  ext v;
  have := congr_arg ( fun f => f ( Pi.single j v ) ) ( hφ a );
  convert congr_arg ( fun f => f i ) this.symm using 1 ; simp +decide [ diagMap_apply ];
  exact congr_arg ( fun f => φ f i ) ( by ext k; simp +decide [ diagMap_apply ] ; by_cases hk : k = j <;> aesop )

/-- matrixEntry is in the centralizer C(A) when φ is A-equivariant. -/
lemma matrixEntry_mem_centralizer {n : ℕ} (φ : Module.End R (Fin n → V))
    (hφ : ∀ (a : A), diagMap (n := n) a.val ∘ₗ φ = φ ∘ₗ diagMap a.val)
    (i j : Fin n) :
    matrixEntry φ i j ∈
      (Subalgebra.centralizer R (↑A : Set (Module.End R V)) : Set (Module.End R V)) := by
  show matrixEntry φ i j ∈ Subalgebra.centralizer R (↑A : Set (Module.End R V))
  rw [Subalgebra.mem_centralizer_iff]
  intro g hg
  exact (matrixEntry_comm_A A φ hφ i j ⟨g, hg⟩).symm

/-
If f ∈ C(C(A)) and φ is A-equivariant on (Fin n → V),
    then diagMap f commutes with φ.
-/
lemma diagMap_comm_of_A_equivariant {n : ℕ}
    (f : Module.End R V)
    (hf : f ∈ Subalgebra.centralizer R
      (↑(Subalgebra.centralizer R (↑A : Set (Module.End R V))) : Set (Module.End R V)))
    (φ : Module.End R (Fin n → V))
    (hφ : ∀ (a : A), diagMap (n := n) a.val ∘ₗ φ = φ ∘ₗ diagMap a.val) :
    diagMap (n := n) f ∘ₗ φ = φ ∘ₗ diagMap f := by
  apply LinearMap.ext; intro w; ext i
  have : f (φ w i) = φ (fun j => f (w j)) i := by
    have h_lhs : f (φ w i) = ∑ j : Fin n, f (matrixEntry φ i j (w j)) := by
      rw [ apply_eq_sum_matrixEntry φ w i, map_sum ]
    have h_rhs : φ (fun j => f (w j)) i = ∑ j : Fin n, matrixEntry φ i j (f (w j)) :=
      apply_eq_sum_matrixEntry φ (fun j => f (w j)) i
    rw [ h_lhs, h_rhs ];
    have h_comm : ∀ j : Fin n, f * matrixEntry φ i j = matrixEntry φ i j * f := by
      exact fun j => hf _ ( matrixEntry_mem_centralizer A φ hφ i j ) |> fun h => by simpa using h.symm;
    exact Finset.sum_congr rfl fun j _ => by simpa using LinearMap.congr_fun ( h_comm j ) ( w j )
  exact this

/-- The A-orbit submodule of w₀ in (Fin n → V). -/
def aOrbit {n : ℕ} (w₀ : Fin n → V) : Submodule R (Fin n → V) :=
  Submodule.span R { w | ∃ a : A, w = fun i => a.val (w₀ i) }

set_option linter.unusedSectionVars false in
/-- w₀ is in its own A-orbit (take a = 1). -/
lemma mem_aOrbit {n : ℕ} (w₀ : Fin n → V) : w₀ ∈ aOrbit A w₀ := by
  apply Submodule.subset_span
  exact ⟨1, by simp⟩

/-
If diagMap f (b) ∈ aOrbit A b and b is a basis, then f ∈ A.
-/
lemma mem_of_diagMap_in_orbit (f : Module.End R V)
    {n : ℕ} (b : Module.Basis (Fin n) R V)
    (h : diagMap (n := n) f (fun i => b i) ∈ aOrbit A (fun i => b i)) :
    f ∈ (A : Set (Module.End R V)) := by
  have h_span_eq_set : Submodule.span R {w | ∃ a : A, w = fun i => a.val (b i)} = {w | ∃ a : A, w = fun i => a.val (b i)} := by
    refine' Set.Subset.antisymm _ _;
    · refine' fun w hw => Submodule.span_induction _ _ _ _ hw;
      · exact fun x hx => hx;
      · exact ⟨ 0, by ext; simp +decide ⟩;
      · rintro x y hx hy ⟨ a, rfl ⟩ ⟨ b, rfl ⟩ ; exact ⟨ a + b, by ext i; simp +decide ⟩ ;
      · rintro a x hx ⟨ a', rfl ⟩;
        exact ⟨ ⟨ a • a', A.smul_mem a'.2 a ⟩, by ext i; simp +decide ⟩;
    · exact fun x hx => Submodule.subset_span hx;
  obtain ⟨a, ha⟩ : ∃ a : A, (fun i => f (b i)) = fun i => a.val (b i) := by
    exact h_span_eq_set.subset h;
  convert a.2;
  exact b.ext fun i => congr_fun ha i

/-- If diagMap f commutes with an idempotent projection p, and w is in the range of p,
    then diagMap f w is in the range of p. -/
lemma diagMap_preserves_range {n : ℕ}
    (f : Module.End R V) (p : Module.End R (Fin n → V))
    (_h_idem : p ∘ₗ p = p)
    (h_comm : diagMap (n := n) f ∘ₗ p = p ∘ₗ diagMap f)
    (w : Fin n → V) (hw : p w = w) :
    p (diagMap f w) = diagMap f w := by
  have := LinearMap.congr_fun h_comm w
  simp at this
  rw [← this, hw]

/-- aOrbit as a Submodule under the A-module structure piModuleA is an A-submodule.
    This means it's closed under the diagMap action. -/
lemma aOrbit_isASubmodule {n : ℕ} (w₀ : Fin n → V) :
    ∀ (a : A) (w : Fin n → V), w ∈ aOrbit A w₀ →
      (fun i => a.val (w i)) ∈ aOrbit A w₀ := by
  intro a w hw;
  refine' Submodule.span_induction _ _ _ _ hw;
  · rintro _ ⟨ b, rfl ⟩;
    exact Submodule.subset_span ⟨ a * b, by ext i; simp +decide [ mul_assoc ] ⟩;
  · simp +decide [ Submodule.zero_mem ];
    exact Submodule.zero_mem _;
  · exact fun x y _hx _hy hx' hy' => by simpa [ map_add ] using Submodule.add_mem _ hx' hy';
  · simp +contextual [ funext_iff, aOrbit ];
    exact fun r x _hx hx' => Submodule.smul_mem _ _ hx'

/-- aOrbit is closed under the diagMap action. -/
lemma aOrbit_A_submodule {n : ℕ} (w₀ : Fin n → V) :
    ∀ (a : A), ∀ w ∈ aOrbit A w₀, diagMap (n := n) a.val w ∈ aOrbit A w₀ := by
  intro a w hw
  exact aOrbit_isASubmodule A w₀ a w hw

/-
If V is semisimple as A-module, then for any A-submodule N of (Fin n → V)
    that is stable under the A-action (diagMap), there exists an R-linear
    idempotent projection p onto N that commutes with diagMap a.val for all a ∈ A.
-/
lemma exists_A_equivariant_proj {n : ℕ}
    (hss : @IsSemisimpleModule A _ V _ (Module.compHom V A.val.toRingHom))
    (N : Submodule R (Fin n → V))
    (hN : ∀ (a : A) (w : Fin n → V), w ∈ N → diagMap (n := n) a.val w ∈ N) :
    ∃ (p : Module.End R (Fin n → V)),
      p ∘ₗ p = p ∧
      (∀ w, w ∈ N ↔ p w = w) ∧
      (∀ (a : A), diagMap (n := n) a.val ∘ₗ p = p ∘ₗ diagMap a.val) := by
  letI : Module A V := Module.compHom V A.val.toRingHom
  haveI : IsSemisimpleModule A V := hss
  obtain ⟨p, hp⟩ : ∃ p : (Fin n → V) →ₗ[A] (Fin n → V), p.comp p = p ∧ (∀ w, w ∈ N ↔ p w = w) := by
    have h_semisimple : IsSemisimpleModule A (Fin n → V) :=
      instIsSemisimpleModuleForallOfFinite (fun _ : Fin n => V)
    have h_complemented : ∀ (N : Submodule A (Fin n → V)), ∃ p : (Fin n → V) →ₗ[A] (Fin n → V), p.comp p = p ∧ (∀ w, w ∈ N ↔ p w = w) := by
      intro N
      obtain ⟨p, hp⟩ : ∃ p : (Fin n → V) →ₗ[A] N, Function.Surjective p ∧ ∀ w : N, p w = w := by
        have := h_semisimple.exists_isCompl N;
        obtain ⟨ Q, hQ ⟩ := this;
        refine' ⟨ _, _, _ ⟩;
        exact N.linearProjOfIsCompl Q hQ;
        · exact Submodule.linearProjOfIsCompl_surjective hQ;
        · aesop;
      refine' ⟨ Submodule.subtype N ∘ₗ p, _, _ ⟩ <;> simp_all +decide [ funext_iff, LinearMap.ext_iff ];
      intro w; specialize hp; have := hp.1; simp_all +decide [ Function.Surjective ] ;
      constructor <;> intro hw <;> simp_all +decide [ Subtype.ext_iff ];
      convert p w |>.2 using 1 ; ext x ; simp +decide [ hw ];
    convert h_complemented ( Submodule.span A { w | w ∈ N } );
    ext w;
    refine' ⟨ fun hw => Submodule.subset_span hw, fun hw => _ ⟩;
    refine' Submodule.span_induction _ _ _ _ hw;
    · exact fun x hx => hx;
    · exact N.zero_mem;
    · exact fun x y hx hy hx' hy' => N.add_mem hx' hy';
    · exact fun a x hx hx' => by simpa [ diagMap_apply ] using hN a x hx';
  refine' ⟨ _, _, _, _ ⟩;
  refine' { toFun := fun w => p w, map_add' := _, map_smul' := _ };
  all_goals norm_num [ funext_iff, LinearMap.ext_iff ] at *;
  · intro m x; exact (by
    convert p.map_smul ( algebraMap R A m ) x using 1);
  · exact hp.1;
  · exact hp.2;
  · intro a ha x i;
    have := p.map_smul ( ⟨ a, ha ⟩ : A ) x;
    convert congr_fun this i |> Eq.symm using 1

/-- Main theorem: C(C(A)) = A when V is semisimple as A-module. -/
theorem centralizer_centralizer_eq
    (hss : @IsSemisimpleModule A _ V _ (Module.compHom V A.val.toRingHom)) :
    Subalgebra.centralizer R ↑(Subalgebra.centralizer R (↑A : Set (Module.End R V))) = A := by
  apply le_antisymm
  · intro f hf
    set n := Module.finrank R V
    have b : Module.Basis (Fin n) R V := Module.finBasis R V
    set w₀ : Fin n → V := fun i => b i
    obtain ⟨p, h_idem, h_range, h_equiv⟩ :=
      exists_A_equivariant_proj A hss (aOrbit A w₀)
        (fun a w hw => aOrbit_A_submodule A w₀ a w hw)
    have h_comm : diagMap (n := n) f ∘ₗ p = p ∘ₗ diagMap f :=
      diagMap_comm_of_A_equivariant A f hf p h_equiv
    have hw₀ : w₀ ∈ aOrbit A w₀ := mem_aOrbit A w₀
    have hpw : p w₀ = w₀ := (h_range w₀).mp hw₀
    have h_in : diagMap (n := n) f w₀ ∈ aOrbit A w₀ := by
      rw [h_range]
      exact diagMap_preserves_range f p h_idem h_comm w₀ hpw
    exact mem_of_diagMap_in_orbit A f b h_in
  · exact Subalgebra.le_centralizer_centralizer R

end Submission.DCTProof

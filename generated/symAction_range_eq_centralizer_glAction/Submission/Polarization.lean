/-
  Proof that centralizer(S_k) ≤ adjoin({f^⊗k}).
-/
import ChallengeDeps

set_option maxHeartbeats 1600000

namespace Submission.Polarization

open scoped TensorProduct
open LeanEval.RepresentationTheory

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
variable {k : ℕ} [Invertible (k.factorial : R)]

/-- Union of two proper submodules is proper (over any ring). -/
lemma union_proper_submodules
    {V : Type*} [AddCommGroup V] [Module R V]
    (V₁ V₂ : Submodule R V) (h1 : V₁ ≠ ⊤) (h2 : V₂ ≠ ⊤) :
    ∃ x : V, x ∉ V₁ ∧ x ∉ V₂ := by
  by_contra! h
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ ∉ V₁ ∧ x₁ ∈ V₂ := by
    exact Exists.imp ( by tauto ) ( SetLike.exists_of_lt ( lt_top_iff_ne_top.mpr h1 ) )
  obtain ⟨x₂, hx₂⟩ : ∃ x₂, x₂ ∉ V₂ ∧ x₂ ∈ V₁ := by
    obtain ⟨x₂, hx₂⟩ : ∃ x₂, x₂ ∉ V₂ := by
      exact not_forall.mp fun h' => h2 <| eq_top_iff.mpr fun x _ => h' x
    exact ⟨x₂, hx₂, Classical.not_not.1 fun hx₂' => hx₂ <| h x₂ hx₂'⟩
  have := h (x₁ + x₂) ?_ <;> simp_all +decide [Submodule.add_mem_iff_right]
  exact fun h' => hx₁.1 (by simpa using V₁.sub_mem h' hx₂.2)

noncomputable def elemEnd {n : ℕ} (b : Module.Basis (Fin n) R M) (a c : Fin n) :
    Module.End R M :=
  (b.coord c).smulRight (b a)

@[simp]
lemma elemEnd_apply_basis {n : ℕ} (b : Module.Basis (Fin n) R M) (a c d : Fin n) :
    elemEnd b a c (b d) = if c = d then b a else 0 := by
  simp [elemEnd]; rw [Finsupp.single_apply]; aesop

lemma map_elemEnd_eq {n : ℕ} (b : Module.Basis (Fin n) R M)
    (p q : Fin k → Fin n) (r : Fin k → Fin n) :
    PiTensorProduct.map (fun i => elemEnd b (p i) (q i))
      (PiTensorProduct.tprod R (fun i => b (r i))) =
    if q = r then PiTensorProduct.tprod R (fun i => b (p i)) else 0 := by
  split_ifs with hq
  · aesop
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hq
    have h_tprod_zero : ∀ (f : Fin k → M), (∃ i, f i = 0) → (PiTensorProduct.tprod R) f = 0 := by
      rintro f ⟨i, hi⟩; exact MultilinearMap.map_coord_zero _ i hi
    convert h_tprod_zero (fun i => elemEnd b (p i) (q i) (b (r i))) ⟨i, _⟩ using 1
    · exact PiTensorProduct.map_tprod _ _
    · simp +decide [elemEnd, hi]

lemma conjugation_eq_compose_perm (fs : Fin k → Module.End R M) (σ : Equiv.Perm (Fin k)) :
    symAction R M k σ⁻¹ * PiTensorProduct.map fs * symAction R M k σ =
      PiTensorProduct.map (fs ∘ σ) := by
  unfold symAction
  ext; simp +decide [Equiv.symm_apply_eq, Equiv.Perm.inv_def]
  grind +splitIndPred

/-
Expansion of map(fun _ => ∑ fs_i) using mapMultilinear + map_sum.
-/
lemma map_diagonal_sum_expand (fs : Fin k → Module.End R M) (S : Finset (Fin k)) :
    PiTensorProduct.map (fun (_ : Fin k) => ∑ i ∈ S, fs i) =
    ∑ g : Fin k → ↑S, PiTensorProduct.map (fun j => fs (g j)) := by
  convert ( MultilinearMap.map_sum ( PiTensorProduct.mapMultilinear R ( fun _ : Fin k => M ) ( fun _ : Fin k => M ) ) fun _ => fun j : S => fs j ) using 1;
  ext; simp +decide [ Finset.sum_attach ] ;

/-
Inclusion-exclusion: coefficient for function h in the double sum.
-/
lemma incl_excl_coeff (h : Fin k → Fin k) :
    ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)),
      (if ∀ i, h i ∈ S then (-1 : R) ^ (k - S.card) else 0) =
    if Function.Surjective h then 1 else 0 := by
  split_ifs with h_surj;
  · rw [ Finset.sum_eq_single ( Finset.univ : Finset ( Fin k ) ) ] <;> simp_all +decide [ Finset.subset_univ ];
    exact fun b hb => by contrapose! hb; exact Finset.eq_univ_of_forall fun x => by obtain ⟨ y, rfl ⟩ := h_surj x; exact hb y;
  · -- Let $A$ be the set of elements in $\text{Fin } k$ that are not in the image of $h$.
    set A := Finset.univ \ Finset.image h Finset.univ with hA_def;
    -- Since $A$ is nonempty, we can rewrite the sum as $\sum_{T \subseteq A} (-1)^{|A| - |T|}$.
    have h_sum_T : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (if ∀ i, h i ∈ S then (-1 : R) ^ (k - S.card) else 0) = ∑ T ∈ Finset.powerset A, (-1 : R) ^ (k - (Finset.univ \ T).card) := by
      rw [ ← Finset.sum_filter ];
      refine' Finset.sum_bij ( fun S hS => Finset.univ \ S ) _ _ _ _ <;> simp_all +decide [ Finset.subset_iff ];
      · exact fun a ha x hx y hy => hx <| hy ▸ ha y;
      · intro a₁ ha₁ a₂ ha₂ h_eq; rw [ ← Finset.sdiff_sdiff_eq_self ( Finset.subset_univ a₁ ), h_eq, Finset.sdiff_sdiff_eq_self ( Finset.subset_univ a₂ ) ] ;
      · intro b hb; use Finset.univ \ b; aesop;
    -- Since $A$ is nonempty, we can rewrite the sum as $\sum_{T \subseteq A} (-1)^{|A| - |T|}$ and use the binomial theorem.
    have h_binom : ∑ T ∈ Finset.powerset A, (-1 : R) ^ (k - (Finset.univ \ T).card) = ∑ T ∈ Finset.powerset A, (-1 : R) ^ (T.card) := by
      refine' Finset.sum_congr rfl fun T hT => _;
      simp +decide [ Finset.card_sdiff ];
      rw [ Nat.sub_sub_self ( le_trans ( Finset.card_le_univ _ ) ( by simp +decide ) ) ];
    have h_binom : ∑ T ∈ Finset.powerset A, (-1 : R) ^ T.card = (1 - 1) ^ A.card := by
      rw [ sub_eq_neg_add, add_pow ] ; norm_num;
      rw [ Finset.sum_powerset ];
      exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_powersetCard ] ; simp +decide [ mul_comm ] ;
    simp_all +decide [ Finset.ext_iff, Function.Surjective ]

/-
The symmetrized pure tensor is in the span of diagonal tensors.
-/
lemma symmetrized_pure_tensor_in_span (fs : Fin k → Module.End R M) :
    ∑ σ : Equiv.Perm (Fin k), PiTensorProduct.map (fs ∘ σ) ∈
      Submodule.span R (Set.range (fun f : M →ₗ[R] M =>
        PiTensorProduct.map (fun _ : Fin k => f))) := by
  -- Show the polarization identity: ∑_σ map(fs ∘ σ) = ∑_S (-1)^{k-|S|} map(fun _ => ∑_{i∈S} fs i)
  -- RHS is a sum of elements in the span, so LHS is in the span.
  rw [ show ( ∑ σ : Equiv.Perm ( Fin k ), PiTensorProduct.map ( fs ∘ σ ) ) = ∑ S ∈ Finset.powerset ( Finset.univ : Finset ( Fin k ) ), ( -1 : R ) ^ ( k - S.card ) • PiTensorProduct.map ( fun _ => ∑ i ∈ S, fs i ) from ?_ ];
  · exact Submodule.sum_mem _ fun S _ => Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ _, rfl ⟩ );
  · have h_sum : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (-1 : R) ^ (k - S.card) • ∑ g : Fin k → S, PiTensorProduct.map (fun j => fs (g j)) = ∑ h : Fin k → Fin k, (∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (if ∀ i, h i ∈ S then (-1 : R) ^ (k - S.card) else 0)) • PiTensorProduct.map (fun j => fs (h j)) := by
      simp +decide [ Finset.sum_smul, Finset.smul_sum ];
      rw [ Finset.sum_comm ];
      refine' Finset.sum_congr rfl fun S _ => _;
      rw [ ← Finset.sum_filter ];
      refine' Finset.sum_bij ( fun x _ => fun i => x i ) _ _ _ _ <;> simp +decide;
      · exact fun a₁ a₂ h => funext fun i => Subtype.ext <| congr_fun h i;
      · exact fun b hb => ⟨ fun i => ⟨ b i, hb i ⟩, rfl ⟩;
    convert h_sum.symm using 1;
    · rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun σ : Equiv.Perm ( Fin k ) => ⇑σ ) Finset.univ ) ) ];
      · rw [ Finset.sum_image ];
        · refine' Finset.sum_congr rfl fun σ _ => _;
          rw [ incl_excl_coeff ];
          simp +decide [ Function.Surjective ];
          exact Eq.symm ( if_pos fun b => ⟨ σ.symm b, by simp +decide ⟩ );
        · exact fun σ _ τ _ h => Equiv.Perm.ext fun x => by simpa using congr_fun h x;
      · intro x hx hx'; rw [ incl_excl_coeff x ] ; simp +decide [ hx' ] ;
        exact fun h => False.elim <| hx' <| Finset.mem_image.mpr ⟨ Equiv.ofBijective x ⟨ Finite.injective_iff_surjective.mpr h, h ⟩, Finset.mem_univ _, rfl ⟩;
    · exact Finset.sum_congr rfl fun _ _ => by rw [ map_diagonal_sum_expand ] ;

/-- Pure tensors span End(V^⊗k). -/
lemma pure_tensor_span_top :
    Submodule.span R (Set.range (fun fs : Fin k → Module.End R M =>
      PiTensorProduct.map fs)) = ⊤ := by
  set n := Module.finrank R M
  set b := Module.finBasis R M
  set tb := Basis.piTensorProduct (fun _ : Fin k => b)
  refine' eq_top_iff.mpr _
  intro T hT
  have hT_decomp : T = ∑ q : Fin k → Fin n, ∑ p : Fin k → Fin n,
      (tb.repr (T (tb q))) p • PiTensorProduct.map (fun i => elemEnd b (p i) (q i)) := by
    refine' tb.ext fun q => _
    simp +decide [map_elemEnd_eq]
    rw [Finset.sum_eq_single q]
    · rw [← tb.linearCombination_repr (T (tb q))]
      rw [Finsupp.linearCombination_apply]
      simp +decide [Finsupp.sum, map_elemEnd_eq]
      rw [Finset.sum_congr rfl]; simp +decide [Finsupp.single_apply]
      rw [Finset.sum_subset (Finset.subset_univ _)]
      · aesop
      · aesop
    · intro p hp hpq
      have h_zero : ∀ x : Fin k → Fin n,
          (PiTensorProduct.map (fun i => elemEnd b (x i) (p i))) (tb q) = 0 := by
        intro x
        have h_zero : (PiTensorProduct.map (fun i => elemEnd b (x i) (p i)))
            (PiTensorProduct.tprod R (fun i => b (q i))) = 0 := by
          rw [map_elemEnd_eq]; aesop
        convert h_zero using 1
        simp +decide [tb, Basis.piTensorProduct_apply]
      aesop
    · exact fun h => False.elim <| h <| Finset.mem_univ q
  exact hT_decomp.symm ▸ Submodule.sum_mem _ fun q _ =>
    Submodule.sum_mem _ fun p _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

/-
The main theorem: centralizer of S_k ≤ adjoin({f^⊗k}).
-/
theorem centralizer_le_adjoin_tensorPow :
    Subalgebra.centralizer R (Set.range (symAction R M k)) ≤
      Algebra.adjoin R (Set.range (fun f : M →ₗ[R] M =>
        PiTensorProduct.map (fun _ : Fin k => f))) := by
  intro T hT
  have hT_comm : ∀ σ : Equiv.Perm (Fin k),
      symAction R M k σ * T = T * symAction R M k σ := by
    intro σ; exact hT (symAction R M k σ) ⟨σ, rfl⟩
  -- Reynolds operator: T = (⅟k!) • ∑_σ σ⁻¹ T σ since T commutes with all σ
  -- But since T commutes, σ⁻¹ T σ = T, so this is trivial.
  -- Instead: T is in span of pure tensors. Apply Reynolds to each.
  -- T ∈ ⊤ = span{map fs} (by pure_tensor_span_top)
  -- Reynolds(T) = (⅟k!) ∑_σ σ⁻¹ T σ = T (by commutativity)
  -- Reynolds is linear, so Reynolds(∑ c_α map(fs_α)) = ∑ c_α Reynolds(map(fs_α))
  -- Reynolds(map fs) = (⅟k!) ∑_σ σ⁻¹(map fs)σ = (⅟k!) ∑_σ map(fs ∘ σ)
  -- Each ∑_σ map(fs ∘ σ) ∈ span{f^⊗k} by symmetrized_pure_tensor_in_span
  -- So T ∈ span{f^⊗k} ⊆ adjoin{f^⊗k}
  have hT_span : T = (⅟(k.factorial : R)) • ∑ σ : Equiv.Perm (Fin k), symAction R M k σ⁻¹ * T * symAction R M k σ := by
    have hT_sum : ∑ σ : Equiv.Perm (Fin k), symAction R M k σ⁻¹ * T * symAction R M k σ = (k.factorial : R) • T := by
      simp +decide [ mul_assoc, hT_comm ];
      simp +decide [ ← mul_assoc, ← map_mul, Fintype.card_perm ];
      norm_cast;
    simp +decide [ hT_sum, smul_smul ];
  -- By pure_tensor_span_top, we can write T as a finite linear combination of pure tensors.
  obtain ⟨Ts, hTs⟩ : ∃ Ts : Finset (Fin k → Module.End R M), T ∈ Submodule.span R (Set.image (fun fs : Fin k → Module.End R M => PiTensorProduct.map fs) Ts) := by
    have hT_span : T ∈ Submodule.span R (Set.range (fun fs : Fin k → Module.End R M => PiTensorProduct.map fs)) := by
      rw [pure_tensor_span_top];
      trivial;
    rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hT_span;
    obtain ⟨ c, rfl ⟩ := hT_span;
    exact ⟨ c.support, Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ( Submodule.subset_span <| Set.mem_image_of_mem _ hi ) ⟩;
  have h_reynolds_span : ∀ fs ∈ Ts, ∑ σ : Equiv.Perm (Fin k), symAction R M k σ⁻¹ * PiTensorProduct.map fs * symAction R M k σ ∈ Submodule.span R (Set.range (fun f : M →ₗ[R] M => PiTensorProduct.map (fun _ : Fin k => f))) := by
    intro fs hfs
    have h_reynolds : ∑ σ : Equiv.Perm (Fin k), symAction R M k σ⁻¹ * PiTensorProduct.map fs * symAction R M k σ = ∑ σ : Equiv.Perm (Fin k), PiTensorProduct.map (fs ∘ σ) := by
      exact Finset.sum_congr rfl fun σ _ => conjugation_eq_compose_perm fs σ;
    exact h_reynolds.symm ▸ symmetrized_pure_tensor_in_span fs;
  have h_reynolds_span : ∑ σ : Equiv.Perm (Fin k), symAction R M k σ⁻¹ * T * symAction R M k σ ∈ Submodule.span R (Set.range (fun f : M →ₗ[R] M => PiTensorProduct.map (fun _ : Fin k => f))) := by
    refine' Submodule.span_induction _ _ _ _ hTs;
    · rintro _ ⟨ fs, hfs, rfl ⟩ ; exact h_reynolds_span fs hfs;
    · simp +decide [ Submodule.zero_mem ];
    · simp +decide [ mul_add, add_mul, Finset.sum_add_distrib ];
      exact fun x y hx hy hx' hy' => Submodule.add_mem _ hx' hy';
    · simp +decide [ mul_smul_comm, smul_mul_assoc ];
      exact fun a x hx hx' => by simpa only [ Finset.smul_sum ] using Submodule.smul_mem _ _ hx';
  rw [hT_span];
  refine' Subalgebra.smul_mem _ _ _;
  convert Submodule.span_le.mpr _ h_reynolds_span;
  rotate_left;
  exact Subalgebra.toSubmodule ( Algebra.adjoin R ( Set.range fun f : M →ₗ[R] M => PiTensorProduct.map fun _ : Fin k => f ) );
  · exact fun x hx => Algebra.subset_adjoin hx;
  · exact rfl

end Submission.Polarization

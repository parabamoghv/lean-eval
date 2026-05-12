/-
  Helper lemmas for proving tensorPow_in_adjoin.
  Key approach: finite difference identity + induction on rank.
-/
import ChallengeDeps

set_option maxHeartbeats 800000

namespace Submission.TensorPowHelpers

open scoped TensorProduct
open LeanEval.RepresentationTheory

variable {R : Type*} [Field R]
variable {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
variable {k : ℕ} [Invertible (k.factorial : R)]

/-
The forward difference identity:
  Σ_{j=0}^k (-1)^{k-j} * C(k,j) * j^m = 0 for m < k
-/
lemma forward_diff_pow_eq_zero {m : ℕ} (hm : m < k) :
    ∑ j ∈ Finset.range (k + 1),
      (-1 : R) ^ (k - j) * (k.choose j : R) * (j : R) ^ m = 0 := by
  -- Prove it first in ℤ by induction on k, then cast to R.
  have h_ind : ∀ (k m : ℕ), m < k → ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - j) * Nat.choose k j * (j : ℤ) ^ m = 0 := by
    intro k m hm; induction' k with k ih generalizing m <;> simp_all +decide [ Finset.sum_range_succ, Nat.choose_succ_succ ] ;
    -- We'll use the fact that $\Delta^{k+1}(x^m) = \Delta^k(\Delta(x^m))$ and $\Delta(x^m) = (x+1)^m - x^m$.
    have h_diff : ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k - j) * Nat.choose k j * ((j + 1 : ℤ) ^ m - j ^ m) = 0 := by
      by_cases h : m = 0 <;> simp_all +decide [ add_pow, mul_sub ];
      simp +decide [ Finset.sum_range_succ, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
      simp +decide [ mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Finset.sum_add_distrib ];
      rw [ Finset.sum_comm ] ; simp_all +decide [ ← mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ; ring;
      rw [ ← Finset.sum_add_distrib ] ; refine' Finset.sum_eq_zero fun i hi => _ ; specialize ih i ( by linarith [ Finset.mem_range.mp hi ] ) ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
      convert congr_arg ( · * ( m.choose i : ℤ ) ) ih using 1 <;> ring;
      simp +decide only [mul_assoc, Finset.mul_sum _ _ _, mul_left_comm];
    have h_split : ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k + 1 - j) * Nat.choose (k + 1) j * j ^ m = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ (k + 1 - j) * Nat.choose k j * j ^ m + ∑ j ∈ Finset.range k, (-1 : ℤ) ^ (k + 1 - (j + 1)) * Nat.choose k j * (j + 1) ^ m := by
      rw [ Finset.sum_range_succ' ];
      rw [ Finset.sum_range_succ' ] ; simp +decide [ Nat.choose_succ_succ, add_mul, mul_add, Finset.sum_add_distrib ] ; ring;
    simp_all +decide [ Finset.sum_range_succ, pow_succ', mul_assoc, mul_sub ];
    rw [ show ( ∑ x ∈ Finset.range k, ( -1 : ℤ ) ^ ( k + 1 - x ) * ( k.choose x * x ^ m ) ) = - ( ∑ x ∈ Finset.range k, ( -1 : ℤ ) ^ ( k - x ) * ( k.choose x * x ^ m ) ) by rw [ ← Finset.sum_neg_distrib ] ; exact Finset.sum_congr rfl fun x hx => by rw [ show k + 1 - x = k - x + 1 by rw [ tsub_add_eq_add_tsub ( Finset.mem_range_le hx ) ] ] ; ring ] at h_split ; linarith;
  simpa using congr_arg ( ( ↑ ) : ℤ → R ) ( h_ind k m hm )

/-
The forward difference identity:
  Σ_{j=0}^k (-1)^{k-j} * C(k,j) * j^k = k!
-/
lemma forward_diff_pow_eq_factorial :
    ∑ j ∈ Finset.range (k + 1),
      (-1 : R) ^ (k - j) * (k.choose j : R) * (j : R) ^ k = (k.factorial : R) := by
  -- We'll use the fact that $\sum_{j=0}^k (-1)^j \binom{k}{j} (k-j)^k = k!$.
  have h_sum : ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (k.choose j) * (k - j) ^ k = (k.factorial : ℤ) := by
    -- We'll use the fact that $\sum_{j=0}^k (-1)^j \binom{k}{j} (k-j)^k$ counts the number of surjective functions from a set of size $k$ to itself.
    have h_surjective : ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (k.choose j) * (k - j : ℤ) ^ k = Finset.card (Finset.filter (fun f : Fin k → Fin k => Function.Surjective f) (Finset.univ : Finset (Fin k → Fin k))) := by
      have h_surjective : Finset.card (Finset.filter (fun f : Fin k → Fin k => Function.Surjective f) (Finset.univ : Finset (Fin k → Fin k))) = ∑ j ∈ Finset.range (k + 1), (-1 : ℤ) ^ j * (k.choose j) * (k - j : ℤ) ^ k := by
        have h_incl_excl : ∀ (S : Finset (Fin k)), Finset.card (Finset.filter (fun f : Fin k → Fin k => ∀ i ∈ S, ¬∃ j, f j = i) (Finset.univ : Finset (Fin k → Fin k))) = (k - S.card : ℤ) ^ k := by
          intro S
          have h_incl_excl_step : Finset.card (Finset.filter (fun f : Fin k → Fin k => ∀ i ∈ S, ¬∃ j, f j = i) (Finset.univ : Finset (Fin k → Fin k))) = Finset.card (Finset.pi (Finset.univ : Finset (Fin k)) (fun _ => Finset.univ \ S)) := by
            refine' Finset.card_bij ( fun f hf => fun i _ => f i ) _ _ _ <;> simp +decide [ funext_iff ];
            · exact fun a ha i hi => ha _ hi _ rfl;
            · exact fun b hb => ⟨ fun x => b x ( Finset.mem_univ x ), fun i hi x => by specialize hb x; aesop, fun x => rfl ⟩;
          simp_all +decide [ Finset.card_sdiff ];
          rw [ Nat.cast_sub ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ]
        have h_incl_excl : Finset.card (Finset.filter (fun f : Fin k → Fin k => Function.Surjective f) (Finset.univ : Finset (Fin k → Fin k))) = ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (-1 : ℤ) ^ S.card * (k - S.card : ℤ) ^ k := by
          have h_incl_excl : ∀ (f : Fin k → Fin k), (if Function.Surjective f then 1 else 0) = ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (-1 : ℤ) ^ S.card * (if ∀ i ∈ S, ¬∃ j, f j = i then 1 else 0) := by
            intro f
            have h_incl_excl_step : ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (-1 : ℤ) ^ S.card * (if ∀ i ∈ S, ¬∃ j, f j = i then 1 else 0) = ∑ S ∈ Finset.powerset (Finset.univ.filter (fun i => ¬∃ j, f j = i)), (-1 : ℤ) ^ S.card := by
              simp +decide [ Finset.sum_ite ];
              congr with x ; simp +decide [ Finset.subset_iff ];
            have h_incl_excl_step : ∀ (S : Finset (Fin k)), ∑ T ∈ Finset.powerset S, (-1 : ℤ) ^ T.card = if S = ∅ then 1 else 0 := by
              exact fun S => Finset.sum_powerset_neg_one_pow_card;
            simp_all +decide [ Function.Surjective ];
          have h_incl_excl : ∑ f : Fin k → Fin k, (if Function.Surjective f then 1 else 0) = ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (-1 : ℤ) ^ S.card * ∑ f : Fin k → Fin k, (if ∀ i ∈ S, ¬∃ j, f j = i then 1 else 0) := by
            rw [ Finset.sum_congr rfl fun f hf => h_incl_excl f, Finset.sum_comm, Finset.sum_congr rfl fun S hS => Finset.mul_sum _ _ _ ];
          convert h_incl_excl using 1;
          · simp +decide [ Finset.sum_ite ];
          · simp +decide [ Finset.sum_ite ];
            grind;
        rw [ h_incl_excl, Finset.sum_powerset ];
        simp +decide [ Finset.sum_powersetCard ];
        exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_congr rfl fun t ht => by rw [ Finset.mem_powersetCard.mp ht |>.2 ] ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.card_univ ] ;
      exact h_surjective.symm;
    rw [ h_surjective ];
    rw [ show ( Finset.univ.filter fun f : Fin k → Fin k => Function.Surjective f ) = Finset.image ( fun f : Equiv.Perm ( Fin k ) => ⇑f ) Finset.univ from ?_, Finset.card_image_of_injective _ fun f g h => by simpa using h ] ; simp +decide [ Fintype.card_perm ];
    ext f; simp [Function.Surjective];
    exact ⟨ fun h => ⟨ Equiv.ofBijective f ⟨ Finite.injective_iff_surjective.mpr h, h ⟩, rfl ⟩, by rintro ⟨ a, rfl ⟩ ; exact a.surjective ⟩;
  convert congr_arg ( fun x : ℤ => x : ℤ → R ) h_sum using 1;
  · rw [ ← Finset.sum_flip ];
    rw [ Finset.sum_congr rfl fun x hx => by rw [ Nat.choose_symm ( Finset.mem_range_succ_iff.mp hx ), tsub_tsub_cancel_of_le ( Finset.mem_range_succ_iff.mp hx ) ] ] ; norm_num;
    exact Finset.sum_congr rfl fun x hx => by rw [ Nat.cast_sub ( Finset.mem_range_succ_iff.mp hx ) ] ;
  · norm_cast

/-
Key identity: the k-th forward difference of (f + j•g)^⊗k equals k!•g^⊗k.
-/
theorem finite_diff_tensorPow (f g : M →ₗ[R] M) :
    ∑ j ∈ Finset.range (k + 1),
      ((-1 : R) ^ (k - j) * (k.choose j : R)) •
        PiTensorProduct.map (fun _ : Fin k => f + (j : R) • g) =
      (k.factorial : R) • PiTensorProduct.map (fun _ : Fin k => g) := by
  ext x;
  simp +decide [ PiTensorProduct.map_tprod ];
  -- Expand each term in the sum using the multinomial theorem.
  have h_expand : ∀ j : ℕ, (PiTensorProduct.tprod R) (fun i => f (x i) + (j : R) • g (x i)) = ∑ s ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (j : R) ^ (Finset.card s) • (PiTensorProduct.tprod R) (fun i => if i ∈ s then g (x i) else f (x i)) := by
    intro j
    have h_expand : (PiTensorProduct.tprod R) (fun i => f (x i) + (j : R) • g (x i)) = ∑ s ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (PiTensorProduct.tprod R) (fun i => if i ∈ s then (j : R) • g (x i) else f (x i)) := by
      have h_expand : ∀ (v : Fin k → M), (PiTensorProduct.tprod R) (fun i => v i + (j : R) • g (x i)) = ∑ s ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (PiTensorProduct.tprod R) (fun i => if i ∈ s then (j : R) • g (x i) else v i) := by
        intro v
        have h_expand : (PiTensorProduct.tprod R) (fun i => v i + (j : R) • g (x i)) = ∑ s : Fin k → Bool, (PiTensorProduct.tprod R) (fun i => if s i then (j : R) • g (x i) else v i) := by
          have h_expand : ∀ (v w : Fin k → M), (PiTensorProduct.tprod R) (fun i => v i + w i) = ∑ s : Fin k → Bool, (PiTensorProduct.tprod R) (fun i => if s i then w i else v i) := by
            intro v w
            have h_expand : (PiTensorProduct.tprod R) (fun i => v i + w i) = ∑ s : Fin k → Bool, (PiTensorProduct.tprod R) (fun i => if s i then w i else v i) := by
              have h_expand : ∀ (i : Fin k), (v i + w i) = ∑ s : Bool, (if s then w i else v i) := by
                simp +decide [ Finset.filter_eq', add_comm ]
              simp +decide only [h_expand];
              exact MultilinearMap.map_sum _ _;
            exact h_expand;
          exact h_expand _ _;
        refine' h_expand.trans ( Finset.sum_bij ( fun s _ => Finset.univ.filter fun i => s i = true ) _ _ _ _ ) <;> simp +decide;
        · simp +contextual [ funext_iff, Finset.ext_iff ];
        · exact fun b => ⟨ fun i => if i ∈ b then Bool.true else Bool.false, by ext; simp +decide ⟩;
      exact h_expand _;
    rw [ h_expand ];
    refine' Finset.sum_congr rfl fun s hs => _;
    have h_expand : ∀ (s : Finset (Fin k)), (PiTensorProduct.tprod R) (fun i => if i ∈ s then (j : R) • g (x i) else f (x i)) = (j : R) ^ (Finset.card s) • (PiTensorProduct.tprod R) (fun i => if i ∈ s then g (x i) else f (x i)) := by
      intro s
      have h_expand : (PiTensorProduct.tprod R) (fun i => if i ∈ s then (j : R) • g (x i) else f (x i)) = (PiTensorProduct.tprod R) (fun i => (if i ∈ s then (j : R) else 1) • (if i ∈ s then g (x i) else f (x i))) := by
        exact congr_arg _ ( funext fun i => by split_ifs <;> simp +decide [ * ] );
      rw [ h_expand ];
      have h_expand : ∀ (c : Fin k → R) (v : Fin k → M), (PiTensorProduct.tprod R) (fun i => c i • v i) = (∏ i, c i) • (PiTensorProduct.tprod R) v := by
        exact fun c v => MultilinearMap.map_smul_univ _ c v;
      convert h_expand _ _ using 2;
      simp +decide [ Finset.prod_ite ];
    exact h_expand s;
  -- Apply the forward difference identity to each term in the sum.
  have h_forward_diff : ∀ s ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (∑ j ∈ Finset.range (k + 1), ((-1 : R) ^ (k - j) * (k.choose j : R)) * (j : R) ^ (Finset.card s)) • (PiTensorProduct.tprod R) (fun i => if i ∈ s then g (x i) else f (x i)) = if s = Finset.univ then (k.factorial : R) • (PiTensorProduct.tprod R) (fun i => g (x i)) else 0 := by
    intro s hs;
    split_ifs with h;
    · simp +decide [ h, forward_diff_pow_eq_factorial ];
    · rw [ forward_diff_pow_eq_zero ];
      · simp +decide;
      · exact lt_of_lt_of_le ( Finset.card_lt_card ( Finset.ssubset_iff_subset_ne.mpr ⟨ Finset.subset_univ s, h ⟩ ) ) ( by simp +decide );
  convert Finset.sum_congr rfl h_forward_diff using 1;
  · simp +decide only [h_expand, Finset.smul_sum, smul_smul, mul_assoc, Finset.sum_smul];
    exact Finset.sum_comm;
  · simp +decide [ Finset.sum_ite, Finset.filter_eq' ]

/-
For nilpotent N, N^⊗k ∈ adjoin(glAction).
-/
theorem nilpotent_tensorPow_in_adjoin {N : M →ₗ[R] M} (hN : IsNilpotent N) :
    PiTensorProduct.map (fun _ : Fin k => N) ∈
      Algebra.adjoin R (Set.range (glAction R M k)) := by
  -- Apply finite_diff_tensorPow with f = LinearMap.id and g = N.
  have h_diff : ∑ j ∈ Finset.range (k + 1),
    ((-1 : R) ^ (k - j) * (k.choose j : R)) • PiTensorProduct.map (fun _ : Fin k => (LinearMap.id + (j : R) • N)) =
    (k.factorial : R) • PiTensorProduct.map (fun _ : Fin k => N) := by
      exact finite_diff_tensorPow LinearMap.id N;
  -- Each term in the sum is in the adjoin of the image of glAction.
  have h_term_in_adjoin : ∀ j ∈ Finset.range (k + 1), PiTensorProduct.map (fun _ : Fin k => (LinearMap.id + (j : R) • N)) ∈ Algebra.adjoin R (Set.range (glAction R M k)) := by
    intro j hj
    have h_unit : IsUnit (LinearMap.id + (j : R) • N) := by
      obtain ⟨ m, hm ⟩ := hN;
      -- Since $N$ is nilpotent, $(j • N)^m = 0$ for some $m$.
      have h_nilpotent : (j • N) ^ m = 0 := by
        rw [ smul_pow, hm, smul_zero ];
      have h_unit : IsUnit (1 + (j • N)) := by
        have h_nilpotent : IsNilpotent (j • N) := by
          exact ⟨ m, h_nilpotent ⟩
        exact h_nilpotent.isUnit_one_add;
      norm_cast;
    exact Algebra.subset_adjoin ⟨ h_unit.unit, rfl ⟩;
  have h_sum_in_adjoin : (k.factorial : R) • PiTensorProduct.map (fun _ : Fin k => N) ∈ Algebra.adjoin R (Set.range (glAction R M k)) := by
    exact h_diff ▸ Subalgebra.sum_mem _ fun j hj => Subalgebra.smul_mem _ ( h_term_in_adjoin j hj ) _;
  convert Subalgebra.smul_mem _ h_sum_in_adjoin ( ⅟ ( k.factorial : R ) ) using 1 ; simp +decide [ smul_smul ]

end Submission.TensorPowHelpers

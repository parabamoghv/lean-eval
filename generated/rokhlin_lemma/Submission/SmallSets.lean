import ChallengeDeps

/-! ## Finding small positive-measure sets

In a non-atomic standard Borel probability space, we can find measurable sets
of arbitrarily small positive measure.
-/

open MeasureTheory Set Function

namespace Submission.SmallSets

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ] [NoAtoms μ]

/-
In a non-atomic finite measure space, any set of positive measure has a measurable
subset of strictly smaller positive measure.
-/
theorem exists_measurableSet_of_lt_measure {s : Set Ω} (hs : MeasurableSet s)
    (hμs : 0 < μ s) :
    ∃ t, MeasurableSet t ∧ t ⊆ s ∧ 0 < μ t ∧ μ t < μ s := by
  -- Let's obtain the countable family of measurable sets separating points.
  obtain ⟨S, hS_countable, hS_measurable, hS_separating⟩ : ∃ S : Set (Set Ω), S.Countable ∧ (∀ s ∈ S, MeasurableSet s) ∧ (∀ x ∈ Set.univ, ∀ y ∈ Set.univ, (∀ s ∈ S, x ∈ s ↔ y ∈ s) → x = y) := by
    exact (MeasurableSpace.CountablySeparated.countably_separated (α := Ω)).exists_countable_separating
  by_cases h : ∀ t ∈ S, μ (s ∩ t) = 0 ∨ μ (s ∩ tᶜ) = 0;
  · -- If for all $t \in S$, $\mu(s \cap t) = 0$ or $\mu(s \cap t^c) = 0$, then $s$ is essentially a single point, contradicting $\mu(s) > 0$.
    have h_single_point : μ (s \ ⋃ t ∈ S, if μ (s ∩ t) = 0 then s ∩ t else s ∩ tᶜ) = μ s := by
      rw [ MeasureTheory.measure_diff_null ];
      exact MeasureTheory.measure_biUnion_null_iff hS_countable |>.2 fun t ht => by cases h t ht <;> aesop;
    -- Since $s \setminus \bigcup_{t \in S} (s \cap t)$ is a subset of $s$ and has measure $\mu(s)$, it must be a singleton set.
    have h_singleton : ∀ x y, x ∈ s \ ⋃ t ∈ S, (if μ (s ∩ t) = 0 then s ∩ t else s ∩ tᶜ) → y ∈ s \ ⋃ t ∈ S, (if μ (s ∩ t) = 0 then s ∩ t else s ∩ tᶜ) → x = y := by
      intro x y hx hy; specialize hS_separating x trivial y trivial; simp_all +decide ;
      grind +ring;
    obtain ⟨x, hx⟩ : ∃ x, x ∈ s \ ⋃ t ∈ S, (if μ (s ∩ t) = 0 then s ∩ t else s ∩ tᶜ) := by
      contrapose! hμs;
      rw [ ← h_single_point, show s \ ⋃ t ∈ S, ( if μ ( s ∩ t ) = 0 then s ∩ t else s ∩ tᶜ ) = ∅ by ext; simp +decide [ hμs ] ] ; norm_num;
    have h_singleton_measure : μ (s \ ⋃ t ∈ S, (if μ (s ∩ t) = 0 then s ∩ t else s ∩ tᶜ)) = μ {x} := by
      exact congr_arg _ ( Set.eq_singleton_iff_unique_mem.mpr ⟨ hx, fun y hy => h_singleton _ _ hy hx ⟩ );
    exact absurd h_singleton_measure ( by rw [ h_single_point ] ; simp [ne_of_gt hμs] );
  · push_neg at h;
    obtain ⟨ t, htS, ht₁, ht₂ ⟩ := h;
    refine' ⟨ s ∩ t, hs.inter ( hS_measurable t htS ), Set.inter_subset_left, _, _ ⟩;
    · exact pos_iff_ne_zero.mpr ht₁;
    · refine' lt_of_le_of_ne ( MeasureTheory.measure_mono ( Set.inter_subset_left ) ) fun h => ht₂ _;
      rw [ show s ∩ tᶜ = s \ ( s ∩ t ) by ext; aesop, MeasureTheory.measure_diff ] <;> norm_num [ h, hs, hS_measurable t htS ]

/-
In a non-atomic standard Borel probability space, for any `δ > 0`, there exists
a measurable set of positive measure at most `δ`.
-/
theorem exists_small_measurableSet {δ : ENNReal} (hδ : 0 < δ) :
    ∃ A, MeasurableSet A ∧ 0 < μ A ∧ μ A ≤ δ := by
  by_contra! h';
  -- By iterating the splitting lemma, we can create a sequence of sets with strictly decreasing measures.
  have h_seq : ∀ n : ℕ, ∃ A : Set Ω, MeasurableSet A ∧ 0 < μ A ∧ μ A ≤ (1 / 2 : ENNReal) ^ n := by
    intro n
    induction' n with n ih;
    · exact ⟨ Set.univ, MeasurableSet.univ, by simp +decide, by simp +decide ⟩;
    · obtain ⟨ A, hA₁, hA₂, hA₃ ⟩ := ih;
      -- Apply the splitting lemma to $A$ to get a subset $B$ with $0 < \mu(B) < \mu(A)$.
      obtain ⟨ B, hB₁, hB₂, hB₃ ⟩ : ∃ B : Set Ω, MeasurableSet B ∧ B ⊆ A ∧ 0 < μ B ∧ μ B < μ A := by
        apply_rules [ exists_measurableSet_of_lt_measure ];
      -- If $\mu(B) \leq \frac{1}{2} \mu(A)$, then we can take $A' = B$.
      by_cases hB_le : μ B ≤ (1 / 2 : ENNReal) * μ A;
      · exact ⟨ B, hB₁, hB₃.1, by rw [ pow_succ' ] ; exact le_trans hB_le ( mul_le_mul_right hA₃ _ ) ⟩;
      · -- If $\mu(B) > \frac{1}{2} \mu(A)$, then we can take $A' = A \setminus B$.
        use A \ B;
        simp_all [ pow_succ' ];
        rw [ MeasureTheory.measure_diff ] <;> norm_num [ hA₁, hB₁, hB₂ ];
        rw [ ← ENNReal.toReal_le_toReal ] at * <;> norm_num at *;
        · rw [ ENNReal.toReal_add ] <;> norm_num at *;
          · rw [ ← ENNReal.toReal_lt_toReal ] at * <;> norm_num at *;
            · exact ⟨ hB₃.2, by linarith ⟩;
            · exact ne_of_lt ( lt_of_lt_of_le ( h' A hA₁ ( by exact lt_of_le_of_ne ( zero_le _ ) ( Ne.symm ( by aesop ) ) ) ) ( le_top ) );
            · exact ne_of_lt ( ENNReal.mul_lt_top ( by norm_num ) ( MeasureTheory.measure_lt_top _ _ ) );
          · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
        · exact ENNReal.mul_ne_top ( by norm_num ) ( by norm_num );
  -- Choose $n$ such that $(1 / 2)^n < \delta$.
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ENNReal) ^ n < δ := by
    have h_lim : Filter.Tendsto (fun n : ℕ => (1 / 2 : ENNReal) ^ n) Filter.atTop (nhds 0) := by
      simp +zetaDelta at *;
    exact ( h_lim.eventually ( gt_mem_nhds hδ ) ) |> fun h => h.exists;
  obtain ⟨ A, hA₁, hA₂, hA₃ ⟩ := h_seq n ; exact not_lt_of_ge hA₃ ( lt_of_lt_of_le hn ( le_of_lt ( h' A hA₁ hA₂ ) ) )

end Submission.SmallSets
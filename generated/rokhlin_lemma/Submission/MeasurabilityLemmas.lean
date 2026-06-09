import ChallengeDeps

/-! ## Measurability lemmas for StandardBorelSpace

In a `StandardBorelSpace`, the σ-algebra is countably separated, which
lets us prove `{x | f x = g x}` is measurable for any two measurable
functions. This gives measurability of fixed-point sets and periodic-point sets.
-/

open MeasureTheory Set Function

namespace Submission.MeasurabilityLemmas

variable {Ω : Type*} [MeasurableSpace Ω]

/-- In a countably separated measurable space (e.g. StandardBorelSpace),
`{x | f x = g x}` is measurable for measurable `f` and `g`. -/
theorem measurableSet_eq_fun_countablySep {β : Type*} [MeasurableSpace β]
    [MeasurableSpace.CountablySeparated β]
    {f g : Ω → β} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {x : Ω | f x = g x} := by
  have hsep := MeasurableSpace.CountablySeparated.countably_separated (α := β)
  obtain ⟨S, hS_count, hS_meas, hS_sep⟩ := hsep.exists_countable_separating
  have heq : {x : Ω | f x = g x} = ⋂ s ∈ S, {x | (f x ∈ s ↔ g x ∈ s)} := by
    ext x
    simp only [mem_setOf_eq, mem_iInter]
    exact ⟨fun h s _ => h ▸ Iff.rfl,
           fun h => hS_sep (f x) (mem_univ _) (g x) (mem_univ _) fun s hs => h s hs⟩
  rw [heq]
  apply MeasurableSet.biInter hS_count
  intro s hs
  have hms := hS_meas s hs
  have : {x : Ω | (f x ∈ s ↔ g x ∈ s)} =
      (f ⁻¹' s ∩ g ⁻¹' s) ∪ ((f ⁻¹' s)ᶜ ∩ (g ⁻¹' s)ᶜ) := by
    ext x; simp [mem_preimage]; tauto
  rw [this]
  exact (hf hms |>.inter (hg hms)) |>.union ((hf hms).compl.inter (hg hms).compl)

variable [StandardBorelSpace Ω]

/-- `{x | T^[n] x = x}` is measurable in a StandardBorelSpace when `T` is measurable. -/
theorem measurableSet_fixedPts_iterate (T : Ω → Ω) (hT : Measurable T) (n : ℕ) :
    MeasurableSet {x : Ω | T^[n] x = x} :=
  measurableSet_eq_fun_countablySep (hT.iterate n) measurable_id

/-- `Function.periodicPts T` is measurable in a StandardBorelSpace when `T` is measurable. -/
theorem measurableSet_periodicPts (T : Ω → Ω) (hT : Measurable T) :
    MeasurableSet (periodicPts T) := by
  have : periodicPts T = ⋃ n ∈ Ioi 0, {x : Ω | T^[n] x = x} := by
    ext x; simp [periodicPts, IsPeriodicPt, IsFixedPt, mem_iUnion, mem_Ioi]
  rw [this]
  exact MeasurableSet.biUnion (to_countable _) fun n _ =>
    measurableSet_fixedPts_iterate T hT n

/-- The complement of `periodicPts` (aperiodic points) is measurable. -/
theorem measurableSet_aperiodic_points (T : Ω → Ω) (hT : Measurable T) :
    MeasurableSet (periodicPts T)ᶜ :=
  (measurableSet_periodicPts T hT).compl

end Submission.MeasurabilityLemmas

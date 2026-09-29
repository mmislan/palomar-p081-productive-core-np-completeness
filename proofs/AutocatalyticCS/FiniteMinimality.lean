module

public import Mathlib.Order.Preorder.Finite

@[expose] public section

/-!
Finite-descent kernel for ordinary-core anchoring and incremental CS
minimality.  The order is instantiated by subnetwork inclusion for ordinary
cores and by child-selection restriction for CS cores.
-/

namespace AutocatalyticCS

variable {α : Type*} [PartialOrder α] [Finite α]

def IsCore (good : α → Prop) (a : α) : Prop :=
  good a ∧ ∀ ⦃b⦄, b < a → ¬ good b

theorem exists_core_le (good : α → Prop) {a : α} (ha : good a) :
    ∃ c ≤ a, IsCore good c := by
  classical
  let candidates : Set α := {x | x ≤ a ∧ good x}
  have hfinite : candidates.Finite := Set.toFinite candidates
  have hnonempty : candidates.Nonempty := ⟨a, le_rfl, ha⟩
  obtain ⟨c, hc_mem, hc_min⟩ := hfinite.exists_minimal hnonempty
  refine ⟨c, hc_mem.1, hc_mem.2, ?_⟩
  intro b hbc hb
  exact (not_lt_of_ge (hc_min ⟨hbc.le.trans hc_mem.1, hb⟩ hbc.le)) hbc

theorem isCore_iff_no_smaller_core (good : α → Prop) (a : α) :
    IsCore good a ↔ good a ∧ ∀ ⦃c⦄, c < a → ¬ IsCore good c := by
  constructor
  · intro ha
    refine ⟨ha.1, ?_⟩
    intro c hca hc
    exact ha.2 hca hc.1
  · rintro ⟨ha, hno⟩
    refine ⟨ha, ?_⟩
    intro b hba hb
    obtain ⟨c, hcb, hc⟩ := exists_core_le good hb
    have hca : c < a := lt_of_le_of_lt hcb hba
    exact hno hca hc

/-- Exact incremental-antichain criterion.  `known` must contain exactly the
smaller cores; no codimension-one deletion premise is used. -/
theorem incremental_minimality (good : α → Prop) (known : Set α) (a : α)
    (hknown : ∀ c, c ∈ known ↔ IsCore good c ∧ c < a) :
    IsCore good a ↔ good a ∧ ∀ c ∈ known, ¬ c < a := by
  rw [isCore_iff_no_smaller_core]
  constructor
  · rintro ⟨ha, hsmaller⟩
    refine ⟨ha, ?_⟩
    intro c hc hca
    exact (hsmaller hca) ((hknown c).mp hc).1
  · rintro ⟨ha, hnone⟩
    refine ⟨ha, ?_⟩
    intro c hca hc
    exact hnone c ((hknown c).2 ⟨hc, hca⟩) hca

end AutocatalyticCS

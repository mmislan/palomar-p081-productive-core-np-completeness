module

public import Mathlib

@[expose] public section

namespace IrrRAFEnumeration.SATCompletion

abbrev Choice (n : Nat) := Fin n × Bool

def conflict {n : Nat} (T : Finset (Choice n)) : Prop :=
  ∃ i, (i, false) ∈ T ∧ (i, true) ∈ T

def covers {n : Nat} (T : Finset (Choice n)) : Prop :=
  ∀ i, ∃ b, (i, b) ∈ T

def hits {n : Nat} (Φ : Finset (Finset (Choice n))) (T : Finset (Choice n)) : Prop :=
  ∀ C ∈ Φ, ∃ x ∈ C, x ∈ T

def eval {n : Nat} (Φ : Finset (Finset (Choice n))) (T : Finset (Choice n)) : Prop :=
  conflict T ∨ covers T ∧ hits Φ T

def pair {n : Nat} (i : Fin n) : Finset (Choice n) := {(i, false), (i, true)}

theorem covers_card {n : Nat} {T : Finset (Choice n)} (h : covers T) : n ≤ T.card := by
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ T.image Prod.fst := by
    intro i _
    obtain ⟨b, hb⟩ := h i
    exact Finset.mem_image.mpr ⟨(i,b), hb, rfl⟩
  have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le)
  simpa using hc

theorem eval_card_two {n : Nat} (hn : 2 ≤ n)
    {Φ : Finset (Finset (Choice n))} {T : Finset (Choice n)}
    (h : eval Φ T) : 2 ≤ T.card := by
  rcases h with ⟨i, hf, ht⟩ | ⟨hcover, _⟩
  · have hsub : pair i ⊆ T := by
      simpa only [pair, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        using And.intro hf ht
    have hc := Finset.card_le_card hsub
    simpa [pair] using hc
  · exact hn.trans (covers_card hcover)

theorem pair_minimal {n : Nat} (hn : 2 ≤ n)
    (Φ : Finset (Finset (Choice n))) (i : Fin n) : Minimal (eval Φ) (pair i) := by
  refine ⟨Or.inl ⟨i, by simp [pair], by simp [pair]⟩, ?_⟩
  intro U hU hsub
  have hcard := eval_card_two hn hU
  have hp : (pair i).card = 2 := by simp [pair]
  have heq : U = pair i := Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [heq]

theorem covers_subset_of_no_conflict {n : Nat} {T U : Finset (Choice n)}
    (hno : ¬ conflict T) (hsub : U ⊆ T) (hc : covers U) : T ⊆ U := by
  rintro ⟨i, b⟩ ht
  obtain ⟨c, hu⟩ := hc i
  have hct := hsub hu
  cases b <;> cases c
  · exact hu
  · exact False.elim (hno ⟨i, ht, hct⟩)
  · exact False.elim (hno ⟨i, hct, ht⟩)
  · exact hu

/-- The minimal true inputs of the monotone SAT gadget are exactly the known
conflict pairs and the consistent satisfying full choices. -/
theorem minimal_eval_iff {n : Nat} (hn : 2 ≤ n)
    (Φ : Finset (Finset (Choice n))) (T : Finset (Choice n)) :
    Minimal (eval Φ) T ↔
      (∃ i, T = pair i) ∨ (¬ conflict T ∧ covers T ∧ hits Φ T) := by
  constructor
  · intro h
    by_cases hc : conflict T
    · obtain ⟨i, hf, ht⟩ := hc
      have hp : pair i ⊆ T := by
        simpa only [pair, Finset.insert_subset_iff, Finset.singleton_subset_iff]
          using And.intro hf ht
      have hrev := h.2 (pair_minimal hn Φ i).1 hp
      exact Or.inl ⟨i, Finset.Subset.antisymm hrev hp⟩
    · exact Or.inr ⟨hc, (h.1.resolve_left hc).1, (h.1.resolve_left hc).2⟩
  · rintro (⟨i, rfl⟩ | ⟨hno, hcov, hhit⟩)
    · exact pair_minimal hn Φ i
    · refine ⟨Or.inr ⟨hcov, hhit⟩, ?_⟩
      intro U hU hsub
      have hnoU : ¬ conflict U := by
        rintro ⟨i, hf, ht⟩
        exact hno ⟨i, hsub hf, hsub ht⟩
      exact covers_subset_of_no_conflict hno hsub (hU.resolve_left hnoU).1

/-- Known-baseline completeness is equivalent to absence of a consistent
satisfying choice. Docking this to a literal CRS is a separate obligation. -/
theorem baseline_complete_iff_unsat {n : Nat} (hn : 2 ≤ n)
    (Φ : Finset (Finset (Choice n))) :
    (∀ T, Minimal (eval Φ) T ↔ ∃ i, T = pair i) ↔
      ¬ ∃ T, ¬ conflict T ∧ covers T ∧ hits Φ T := by
  constructor
  · intro hcomplete
    rintro ⟨T, hno, hc, hh⟩
    have hmin := (minimal_eval_iff hn Φ T).mpr (Or.inr ⟨hno, hc, hh⟩)
    obtain ⟨i, heq⟩ := (hcomplete T).mp hmin
    apply hno
    rw [heq]
    exact ⟨i, by simp [pair], by simp [pair]⟩
  · intro hunsat T
    rw [minimal_eval_iff hn Φ T]
    constructor
    · rintro (hp | hs)
      · exact hp
      · exact False.elim (hunsat ⟨T, hs⟩)
    · exact Or.inl

end IrrRAFEnumeration.SATCompletion

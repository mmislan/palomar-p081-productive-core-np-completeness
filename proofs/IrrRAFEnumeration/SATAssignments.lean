module

public import proofs.IrrRAFEnumeration.SATReduction

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open SATCompletion

def assignmentSet {n : Nat} (f : Fin n → Bool) : Finset (Choice n) :=
  Finset.univ.image (fun i => (i, f i))

@[simp] theorem mem_assignmentSet {n : Nat} (f : Fin n → Bool) (x : Choice n) :
    x ∈ assignmentSet f ↔ f x.1 = x.2 := by
  rcases x with ⟨i,b⟩
  simp [assignmentSet]

def Satisfies {n m : Nat} (Φ : Fin m → Finset (Choice n)) (f : Fin n → Bool) : Prop :=
  ∀ j, ∃ x ∈ Φ j, f x.1 = x.2

theorem assignmentSet_no_conflict {n : Nat} (f : Fin n → Bool) : ¬ conflict (assignmentSet f) := by
  rintro ⟨i, hf, ht⟩
  simp only [mem_assignmentSet] at hf ht
  rw [hf] at ht
  cases ht

theorem assignmentSet_covers {n : Nat} (f : Fin n → Bool) : covers (assignmentSet f) := by
  intro i
  exact ⟨f i, by simp⟩

theorem assignmentSet_hits_iff {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (f : Fin n → Bool) : hits (family Φ) (assignmentSet f) ↔ Satisfies Φ f := by
  constructor
  · intro h j
    obtain ⟨x, hx, hxt⟩ := h (Φ j) (by simp [family])
    exact ⟨x, hx, (mem_assignmentSet f x).mp hxt⟩
  · intro h C hC
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨x, hx, he⟩ := h j
    exact ⟨x, hx, (mem_assignmentSet f x).mpr he⟩

theorem exists_assignmentSet_of_consistent_cover {n : Nat} (T : Finset (Choice n))
    (hno : ¬ conflict T) (hc : covers T) : ∃ f, T = assignmentSet f := by
  classical
  choose f hf using hc
  refine ⟨f, Finset.Subset.antisymm ?_ ?_⟩
  · intro x hx
    apply (mem_assignmentSet f x).mpr
    have hfx := hf x.1
    rcases x with ⟨i,b⟩
    cases hb : b <;> cases hfi : f i
    · rfl
    · exact False.elim (hno ⟨i, by simpa [hb] using hx, by simpa [hfi] using hfx⟩)
    · exact False.elim (hno ⟨i, by simpa [hfi] using hfx, by simpa [hb] using hx⟩)
    · rfl
  · intro x hx
    have he := (mem_assignmentSet f x).mp hx
    have hfx := hf x.1
    simpa [he] using hfx

theorem consistent_satisfying_iff_assignment {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    (∃ T, ¬ conflict T ∧ covers T ∧ hits (family Φ) T) ↔ ∃ f, Satisfies Φ f := by
  constructor
  · rintro ⟨T, hno, hc, hh⟩
    obtain ⟨f, rfl⟩ := exists_assignmentSet_of_consistent_cover T hno hc
    exact ⟨f, (assignmentSet_hits_iff Φ f).mp hh⟩
  · rintro ⟨f, hf⟩
    exact ⟨assignmentSet f, assignmentSet_no_conflict f, assignmentSet_covers f,
      (assignmentSet_hits_iff Φ f).mpr hf⟩

theorem literal_baseline_complete_iff_cnf_unsat {n m : Nat} (hn : 2 ≤ n)
    (Φ : Fin m → Finset (Choice n)) :
    (∀ S, MinRAFApprox.SetCoverSource.IsIrreducibleRAF (CircuitSource.crs (rules Φ))
      CircuitSource.catalysis S ↔ ∃ i : Fin n, S = sourceSet (m := m) (pair i)) ↔
      ¬ ∃ f : Fin n → Bool, Satisfies Φ f := by
  rw [literal_baseline_complete_iff_unsat hn Φ, consistent_satisfying_iff_assignment]

end IrrRAFEnumeration.SATSource

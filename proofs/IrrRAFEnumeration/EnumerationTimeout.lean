module

public import proofs.IrrRAFEnumeration.SATFamily

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open RAF SATCompletion CircuitSource

/-- Encoded output length may be any fixed source-dependent length function.
The timeout lemma does not identify number of outputs with bit length. -/
def BoundedRunCorrect {α : Type*} (answer : α) (run : Nat → Option α) : Prop :=
  (∀ t value, run t = some value → value = answer) ∧
  (∀ t u value, t ≤ u → run t = some value → run u = some value)

/-- Generic total-time argument. The algorithm may emit no answer before
termination; no polynomial-delay or output-order assumption is used. -/
theorem timeout_eq_baseline_iff {α : Type*} (answer base : α)
    (run : Nat → Option α) (cost : α → Nat) (bound : Nat → Nat)
    (hcorrect : BoundedRunCorrect answer run)
    (htotal : ∃ t ≤ bound (cost answer), run t = some answer) :
    run (bound (cost base)) = some base ↔ answer = base := by
  constructor
  · intro h
    exact (hcorrect.1 _ _ h).symm
  · intro h
    subst answer
    obtain ⟨t, ht, hrun⟩ := htotal
    exact hcorrect.2 _ _ _ ht hrun

/-- A bounded simulation of any exact total-time irrRAF enumerator decides
UNSAT on the literal source using the known baseline's encoded size. This is
the semantic timeout reduction; machine-cost realization is not assumed here. -/
theorem bounded_enumerator_decides_unsat {n m : Nat} (hn : 2 ≤ n)
    (Φ : Fin m → Finset (Choice n))
    (run : Nat → Option (Finset (Finset
      (Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))))))
    (encodedLength : Finset (Finset
      (Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)))) → Nat)
    (bound : Nat → Nat)
    (hcorrect : BoundedRunCorrect (irrRAFFamily (crs (rules Φ)) catalysis) run)
    (htotal : ∃ t ≤ bound (encodedLength (irrRAFFamily (crs (rules Φ)) catalysis)),
      run t = some (irrRAFFamily (crs (rules Φ)) catalysis)) :
    run (bound (encodedLength (baseline n m))) = some (baseline n m) ↔
      ¬ ∃ T, ¬ conflict T ∧ covers T ∧ hits (family Φ) T := by
  rw [timeout_eq_baseline_iff _ _ run encodedLength bound hcorrect htotal,
    irrRAFFamily_eq_baseline_iff_unsat hn Φ]

end IrrRAFEnumeration.SATSource

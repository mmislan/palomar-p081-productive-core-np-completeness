module

public import proofs.IrrRAFEnumeration.SATAssignments
public import proofs.IrrRAFEnumeration.SATSourceSize
public import proofs.IrrRAFEnumeration.EnumerationTimeout

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open RAF SATCompletion CircuitSource

/-- The general literal SAT reduction with actual polynomial source size,
valid baseline outputs, exact output length, and ordinary Boolean CNF UNSAT.
This is the finite reduction theorem, not a definition of the classes P/NP. -/
theorem sat_reduction_with_polynomial_source {n m : Nat} (hn : 2 ≤ n)
    (Φ : Fin m → Finset (Choice n)) :
    literalIncidences Φ ≤ 300 * (n+m+1)^4 ∧
    (baseline n m).card = n ∧
    (∑ S ∈ baseline n m, S.card) = n * (3*n + 2*n*m + 4) ∧
    baseline n m ⊆ irrRAFFamily (crs (rules Φ)) catalysis ∧
    (irrRAFFamily (crs (rules Φ)) catalysis = baseline n m ↔
      ¬ ∃ f : Fin n → Bool, Satisfies Φ f) := by
  refine ⟨literalIncidences_polynomial Φ, baseline_card n m, ?_,
    baseline_subset_irrRAFFamily hn Φ, ?_⟩
  · rw [baseline_output_incidence, step_card]
  · rw [irrRAFFamily_eq_baseline_iff_unsat hn Φ, consistent_satisfying_iff_assignment]

/-- Composed bounded-simulation decision theorem on actual Boolean CNF
assignments. Correctness and total runtime of the hypothetical enumerator are
explicit hypotheses; no polynomial-time SAT decision is assumed. -/
theorem bounded_enumerator_decides_cnf_unsat {n m : Nat} (hn : 2 ≤ n)
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
      ¬ ∃ f : Fin n → Bool, Satisfies Φ f := by
  rw [bounded_enumerator_decides_unsat hn Φ run encodedLength bound hcorrect htotal,
    consistent_satisfying_iff_assignment]

end IrrRAFEnumeration.SATSource

module

public import proofs.IrrRAFEnumeration.SATUniformCompiler
public import proofs.IrrRAFEnumeration.EnumerationTimeout

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open RAF SATCompletion CircuitSource

/-- Inclusion of the known family makes its cardinality a sufficient
completeness observation. No output ordering is involved. -/
theorem irrRAFFamily_card_eq_iff_cnf_unsat {n m : Nat} (hn : 2 ≤ n)
    (Φ : Fin m → Finset (Choice n)) :
    (irrRAFFamily (crs (rules Φ)) catalysis).card = n ↔
      ¬ ∃ f : Fin n → Bool, Satisfies Φ f := by
  have hcard : (irrRAFFamily (crs (rules Φ)) catalysis).card = n ↔
      irrRAFFamily (crs (rules Φ)) catalysis = baseline n m := by
    constructor
    · intro h
      exact (Finset.eq_of_subset_of_card_le (baseline_subset_irrRAFFamily hn Φ)
        (by rw [h,baseline_card])).symm
    · intro h
      rw [h,baseline_card]
  rw [hcard,irrRAFFamily_eq_baseline_iff_unsat hn Φ,consistent_satisfying_iff_assignment]

def fixedWidthOutputLength (R count : Nat) : Nat := count+1+count*R

/-- The timeout's numeric output budget can be computed without producing
the baseline string. This is its actual encoded length, not just output count. -/
theorem countTimeout_length_polynomial {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    fixedWidthOutputLength (reactionCount n m) n ≤ 20*(cnfBits Φ).length^3 := by
  have h := baseline_length_in_input_bits Φ
  rw [baselineBits_length] at h
  exact h

/-- Correct completed family observations induce correct count observations.
A machine implementation must count duplicate-free completed records. -/
theorem boundedRunCorrect_card {α : Type} (answer : Finset α)
    (run : Nat → Option (Finset α)) (h : BoundedRunCorrect answer run) :
    BoundedRunCorrect answer.card (fun t => (run t).map Finset.card) := by
  constructor
  · intro t value hv
    cases he : run t with
    | none => simp [he] at hv
    | some s =>
        have hs := h.1 t s he
        subst s
        simpa [he] using hv.symm
  · intro t u value htu hv
    cases he : run t with
    | none => simp [he] at hv
    | some s =>
        have hu := h.2 t u s htu he
        simpa [he,hu] using hv

/-- Numeric count-only timeout reduction for the actual CNF source. No
baseline-output constructor or family comparison is a premise. Concrete
counting, clock and simulation costs are still separate obligations. -/
theorem bounded_count_decides_cnf_unsat {n m : Nat} (hn : 2 ≤ n)
    (Φ : Fin m → Finset (Choice n)) (run : Nat → Option Nat) (bound : Nat → Nat)
    (hcorrect : BoundedRunCorrect (irrRAFFamily (crs (rules Φ)) catalysis).card run)
    (htotal : ∃ t ≤ bound (fixedWidthOutputLength (reactionCount n m)
        (irrRAFFamily (crs (rules Φ)) catalysis).card),
      run t = some (irrRAFFamily (crs (rules Φ)) catalysis).card) :
    run (bound (fixedWidthOutputLength (reactionCount n m) n)) = some n ↔
      ¬ ∃ f : Fin n → Bool, Satisfies Φ f := by
  rw [timeout_eq_baseline_iff _ n run (fixedWidthOutputLength (reactionCount n m))
    bound hcorrect htotal,irrRAFFamily_card_eq_iff_cnf_unsat hn Φ]

end IrrRAFEnumeration.SATSource

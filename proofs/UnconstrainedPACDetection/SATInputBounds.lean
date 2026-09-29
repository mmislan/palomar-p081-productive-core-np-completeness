module

public import proofs.Complexitylib.SAT.Encoding

@[expose] public section

/-! Syntax-size bounds for the fixed unary-variable SAT encoding. These are
inputs to a graph-construction size proof, not a runtime or reduction theorem. -/

namespace UnconstrainedPACDetection.SATInputBounds

open Complexity.SAT

def occurrences (φ : CNF) : Nat := φ.foldr (fun c n => c.length + n) 0

theorem clause_length_bound (c : Clause) : 4 * c.length ≤ c.encode.length := by
  induction c with
  | nil => simp
  | cons l c ih =>
    simp only [Clause.encode_cons, List.length_append, List.length_cons,
      List.length_nil, doubleBits_length, Lit.encodeRaw_length]
    omega

theorem syntax_length_bound (φ : CNF) :
    2 * φ.length + 4 * occurrences φ ≤ φ.encode.length := by
  induction φ with
  | nil => simp [occurrences]
  | cons c φ ih =>
    have hc := clause_length_bound c
    simp only [CNF.encode_cons, List.length_append, List.length_cons,
      List.length_nil, occurrences, List.foldr_cons] at *
    omega

theorem variable_clause_grid_bound (φ : CNF) :
    (φ.maxVar + 1) * φ.length ≤ (φ.encode.length + 1) * φ.encode.length := by
  have hsyntax := syntax_length_bound φ
  have hclauses : φ.length ≤ φ.encode.length := by omega
  exact Nat.mul_le_mul (Nat.add_le_add_right (CNF.maxVar_le_encode_length φ) 1) hclauses

end UnconstrainedPACDetection.SATInputBounds

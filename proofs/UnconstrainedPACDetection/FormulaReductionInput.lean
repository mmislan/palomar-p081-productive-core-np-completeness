module

public import proofs.UnconstrainedPACDetection.FormulaSyntaxMachine
public import proofs.UnconstrainedPACDetection.FormulaPACEncoding
public import proofs.Complexitylib.Classes.P.PairWithInput

@[expose] public section

namespace UnconstrainedPACDetection.FormulaReductionInput
open Complexity SAT

/-- Polynomial prelude: validation flag paired with the unchanged raw input. -/
def prepare (xs : List Bool) : List Bool := pair [(CNF.decode? xs).isSome] xs

theorem prepare_mem_FP : prepare ∈ FP :=
  mem_FP_pairWithInput FormulaSyntax.syntax_mem_FP

theorem prepare_length (xs : List Bool) : (prepare xs).length = xs.length+4 := by
  simp [prepare]; omega

theorem prepare_decode (xs : List Bool) :
    unpair? (prepare xs) = some ([(CNF.decode? xs).isSome],xs) := by
  exact unpair?_pair _ _

/-- The false guard selects exactly the established malformed-input fallback. -/
theorem rejected_output (xs : List Bool)
    (h : unpair? (prepare xs) = some ([false],xs)) :
    FormulaPACEncoding.compile xs = FormulaPACEncoding.encode [[]] := by
  rw [prepare_decode] at h
  cases hd : CNF.decode? xs with
  | none => simp [FormulaPACEncoding.compile,hd]
  | some φ => simp [hd] at h

/-- A true guard supplies an actual decoded formula and preserves its original bits. -/
theorem accepted_input (xs : List Bool)
    (h : unpair? (prepare xs) = some ([true],xs)) :
    ∃ φ : CNF, CNF.decode? xs = some φ ∧ xs = φ.encode := by
  rw [prepare_decode] at h
  cases hd : CNF.decode? xs with
  | none => simp [hd] at h
  | some φ => exact ⟨φ,rfl,CNF.decode?_sound hd⟩

end UnconstrainedPACDetection.FormulaReductionInput

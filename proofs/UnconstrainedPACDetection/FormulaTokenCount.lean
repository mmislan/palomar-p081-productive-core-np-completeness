module

public import proofs.UnconstrainedPACDetection.FormulaEnumeration
public import proofs.UnconstrainedPACDetection.FormulaSyntaxMachine

@[expose] public section

namespace UnconstrainedPACDetection.FormulaTokenCount
open Complexity SAT

/-- `false` selects literal separators; `true` selects clause separators. -/
def hit (sep : Bool) : Option Bool → Bool → Bool
  | none, _ => false
  | some a, b => (a == sep) && (b == !sep)

def next : Option Bool → Bool → Option Bool
  | none,b => some b
  | some _,_ => none

def run (sep : Bool) : Option Bool → List Bool → Nat
  | _,[] => 0
  | q,b::bs => (if hit sep q b then 1 else 0) + run sep (next q b) bs

theorem doubled_append (sep : Bool) (bs rest : List Bool) :
    run sep none (doubleBits bs ++ rest) = run sep none rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases sep <;> cases b <;> simpa [doubleBits_cons,run,next,hit] using ih

theorem clause_append (sep : Bool) (c : Clause) (rest : List Bool) :
    run sep none (c.encode ++ rest) = (if sep then 0 else c.length) + run sep none rest := by
  induction c with
  | nil => simp [Clause.encode]
  | cons l c ih =>
    simp only [Clause.encode_cons,List.append_assoc,doubled_append]
    cases sep <;> simp [run,next,hit,ih,Nat.add_assoc]
    omega

theorem formula_count (sep : Bool) (φ : CNF) :
    run sep none φ.encode = if sep then φ.length else SATInputBounds.occurrences φ := by
  induction φ with
  | nil => simp [CNF.encode,run,SATInputBounds.occurrences]
  | cons c φ ih =>
    simp only [CNF.encode_cons,List.append_assoc,clause_append]
    cases sep <;> simp [run,next,hit,ih,SATInputBounds.occurrences,Nat.add_comm]

theorem decoded_counts (xs : List Bool) (φ : CNF) (h : CNF.decode? xs = some φ) :
    run true none xs = φ.length ∧ run false none xs + 1 = FormulaWiring.levels φ := by
  have he := CNF.decode?_sound h
  subst xs
  simp only [formula_count,↓reduceIte,FormulaWiring.levels,FormulaEnumeration.occurrence_count]
  exact ⟨True.intro,rfl⟩

theorem run_bound (sep : Bool) (q : Option Bool) (xs : List Bool) :
    run sep q xs ≤ xs.length := by
  induction xs generalizing q with
  | nil => rfl
  | cons b bs ih =>
    have h := ih (next q b)
    simp only [run,List.length_cons]
    split <;> omega

end UnconstrainedPACDetection.FormulaTokenCount

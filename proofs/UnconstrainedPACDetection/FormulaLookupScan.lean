module

public import proofs.UnconstrainedPACDetection.FormulaOccurrenceLookup
public import proofs.UnconstrainedPACDetection.FormulaTokenCountMachine

@[expose] public section

namespace UnconstrainedPACDetection.FormulaLookupScan
open Complexity SAT

inductive Event where
  | pending (b : Bool) | data (b : Bool) | literal | clause
  deriving DecidableEq, Fintype

def event (q : Option Bool) (b : Bool) : Event :=
  match q with
  | none => .pending b
  | some a => if a = b then .data a else if a then .clause else .literal

structure Result where
  raw : List Bool
  clauses : Nat
  remaining : Nat
  deriving DecidableEq

/-- One pass stops at the selected literal separator. The syntax guard is separate. -/
def run : Option Bool → Nat → List Bool → Result
  | _,i,[] => ⟨[],0,i⟩
  | q,i,b::xs =>
    match event q b with
    | .pending a => run (some a) i xs
    | .data a =>
      let r := run none i xs
      ⟨(if i = 0 then [a] else []) ++ r.raw,r.clauses,r.remaining⟩
    | .literal => if i = 0 then ⟨[],0,0⟩ else run none (i-1) xs
    | .clause =>
      let r := run none i xs
      ⟨r.raw,r.clauses+1,r.remaining⟩

theorem doubled (bs rest : List Bool) (i : Nat) :
    run none i (doubleBits bs ++ rest) =
      let r := run none i rest
      ⟨(if i = 0 then bs else []) ++ r.raw,r.clauses,r.remaining⟩ := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    simp only [doubleBits_cons,List.cons_append,run,event,↓reduceIte]
    rw [ih]
    by_cases hi : i = 0 <;> simp [hi]

theorem literal (l : Lit) (rest : List Bool) (i : Nat) :
    run none i (doubleBits l.encodeRaw ++ ([false,true] ++ rest)) =
      if i = 0 then ⟨l.encodeRaw,0,0⟩ else run none (i-1) rest := by
  rw [doubled]
  by_cases hi : i = 0 <;> simp [run,event,hi]

theorem clause (ls : Clause) (rest : List Bool) (i : Nat) :
    run none i (ls.encode ++ rest) =
      if h : i < ls.length then ⟨ls[i].encodeRaw,0,0⟩
      else run none (i-ls.length) rest := by
  induction ls generalizing i with
  | nil => simp
  | cons l ls ih =>
    simp only [Clause.encode_cons,List.append_assoc,literal]
    cases i with
    | zero => simp
    | succ i =>
      simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,Nat.add_sub_cancel]
      rw [ih]
      by_cases hi : i < ls.length <;> simp [hi]

def decode (r : Result) : Option (Nat × Lit) :=
  (Lit.decodeRaw? r.raw).map (fun l => (r.clauses,l))

/-- Exact consumer interface: the output data and clause counter identify an occurrence. -/
theorem formula_result (φ : CNF) (i c : Nat) :
    (Lit.decodeRaw? (run none i φ.encode).raw).map
      (fun l => (c+(run none i φ.encode).clauses,l)) =
      (FormulaOccurrenceLookup.indexedFrom c φ)[i]? := by
  induction φ generalizing i c with
  | nil => simp [run,FormulaOccurrenceLookup.indexedFrom,Lit.decodeRaw?]
  | cons ls φ ih =>
    simp only [CNF.encode_cons,List.append_assoc,clause,
      FormulaOccurrenceLookup.indexedFrom,List.getElem?_append,List.length_map]
    by_cases hi : i < ls.length
    · simp [hi]
    · simp only [dite_eq_right hi,ite_eq_right hi,List.cons_append,List.nil_append,run,event,
        Bool.true_eq_false,↓reduceIte]
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (i-ls.length) (c+1)

theorem decoded_lookup (xs : List Bool) (φ : CNF) (h : CNF.decode? xs = some φ) (i : Nat) :
    decode (run none i xs) = (FormulaWiring.occurrences φ)[i]? := by
  have he := CNF.decode?_sound h
  subst xs
  simpa [decode,FormulaOccurrenceLookup.occurrences_eq] using formula_result φ i 0

end UnconstrainedPACDetection.FormulaLookupScan

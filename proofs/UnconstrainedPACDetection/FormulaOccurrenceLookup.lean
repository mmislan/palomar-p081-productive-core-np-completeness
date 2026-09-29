module

public import proofs.UnconstrainedPACDetection.FormulaEnumeration
public import proofs.Complexitylib.SAT.Verifier

@[expose] public section

namespace UnconstrainedPACDetection.FormulaOccurrenceLookup
open Complexity SAT

/-- Direct scan. The syntax guard is responsible for rejecting malformed whole inputs. -/
def seek : Nat → Nat → Option Bool → Nat → List Bool → Option (Nat × Lit)
  | _,_,_,_,[] => none
  | _,_,_,_,[_] => none
  | i,c,s,v,a::b::bs =>
      if a = b then
        match s with
        | none => seek i c (some a) 0 bs
        | some sign => seek i c (some sign) (v+1) bs
      else if a then
        match s with
        | none => seek i (c+1) none 0 bs
        | some _ => none
      else match s with
        | none => none
        | some sign => if i = 0 then some (c,⟨sign,v⟩) else seek (i-1) c none 0 bs

def indexedFrom : Nat → CNF → List (Nat × Lit)
  | _,[] => []
  | c,ls::φ => ls.map (fun l => (c,l)) ++ indexedFrom (c+1) φ

theorem indexedFrom_eq (c : Nat) (φ : CNF) :
    indexedFrom c φ = (φ.zipIdx c).flatMap (fun z => z.1.map (fun l => (z.2,l))) := by
  induction φ generalizing c with
  | nil => rfl
  | cons ls φ ih => simp [indexedFrom,List.zipIdx_cons,ih]

theorem occurrences_eq (φ : CNF) : indexedFrom 0 φ = FormulaWiring.occurrences φ :=
  indexedFrom_eq 0 φ

theorem unary_seek (i c : Nat) (s : Bool) (v k : Nat) (rest : List Bool) :
    seek i c (some s) k (doubleBits (List.replicate v true) ++ rest) =
      seek i c (some s) (k+v) rest := by
  induction v generalizing k with
  | zero => simp
  | succ v ih =>
    simp only [List.replicate_succ,doubleBits_cons,List.cons_append,seek,↓reduceIte]
    rw [ih]
    congr 1
    omega

theorem literal_seek (i c : Nat) (l : Lit) (rest : List Bool) :
    seek i c none 0 (doubleBits l.encodeRaw ++ ([false,true] ++ rest)) =
      if i = 0 then some (c,l) else seek (i-1) c none 0 rest := by
  obtain ⟨s,v⟩ := l
  simp only [Lit.encodeRaw,Unary.encode,doubleBits_cons,List.cons_append]
  cases s <;> simp only [seek,↓reduceIte]
  all_goals rw [unary_seek i c _ v 0]
  all_goals simp [seek]

theorem clause_seek (ls : Clause) (i c : Nat) (rest : List Bool) :
    seek i c none 0 (ls.encode ++ rest) =
      if h : i < ls.length then some (c,ls[i]) else seek (i-ls.length) c none 0 rest := by
  induction ls generalizing i with
  | nil => simp
  | cons l ls ih =>
    simp only [Clause.encode_cons,List.append_assoc,literal_seek]
    cases i with
    | zero => simp
    | succ i =>
      simp only [Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,Nat.add_sub_cancel]
      rw [ih]
      by_cases hi : i < ls.length <;> simp [hi]

theorem formula_seek (φ : CNF) (i c : Nat) :
    seek i c none 0 φ.encode = (indexedFrom c φ)[i]? := by
  induction φ generalizing i c with
  | nil => simp [seek,indexedFrom]
  | cons ls φ ih =>
    simp only [CNF.encode_cons,List.append_assoc,clause_seek,indexedFrom,
      List.getElem?_append,List.length_map]
    by_cases hi : i < ls.length
    · simp [hi]
    · simp only [dite_eq_right hi,ite_eq_right hi,List.cons_append,List.nil_append,seek,
        Bool.true_eq_false,↓reduceIte]
      exact ih (i-ls.length) (c+1)

theorem decoded_lookup (xs : List Bool) (φ : CNF) (h : CNF.decode? xs = some φ) (i : Nat) :
    seek i 0 none 0 xs = (FormulaWiring.occurrences φ)[i]? := by
  have he := CNF.decode?_sound h
  subst xs
  rw [formula_seek,occurrences_eq]

theorem wiring_lookup (φ : CNF) (i : Fin (FormulaWiring.levels φ)) :
    seek i.val 0 none 0 φ.encode = FormulaWiring.lookup φ i := by
  rw [formula_seek,occurrences_eq]
  rfl

theorem dummy_lookup (φ : CNF) :
    seek (FormulaWiring.occurrences φ).length 0 none 0 φ.encode = none := by
  rw [formula_seek,occurrences_eq]
  simp

end UnconstrainedPACDetection.FormulaOccurrenceLookup

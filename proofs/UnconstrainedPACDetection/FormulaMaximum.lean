module

public import proofs.UnconstrainedPACDetection.FormulaTokenCountMachine

@[expose] public section

namespace UnconstrainedPACDetection.FormulaMaximum
open Complexity SAT

abbrev ScanState := Bool × Option Bool

inductive Action where
  | keep (q : ScanState) | advance | reset
  deriving DecidableEq

def action (q : ScanState) (b : Bool) : Action :=
  match q.2 with
  | none => .keep (q.1,some b)
  | some a => if a = b then (if q.1 then .advance else .keep (true,none)) else .reset

/-- Current identifier length and the maximum so far are distinct state variables. -/
def scan : ScanState → Nat → Nat → List Bool → Nat
  | _,_,mx,[] => mx
  | q,k,mx,b::bs => match action q b with
      | .keep q' => scan q' k mx bs
      | .advance => scan (true,none) (k+1) (max mx (k+1)) bs
      | .reset => scan (false,none) 0 mx bs

/-- Exact planned transition budget: reset rewinds a head at k+1 to cell 1. -/
def cost : ScanState → Nat → List Bool → Nat
  | _,_,[] => 1
  | q,k,b::bs => match action q b with
      | .keep q' => 1 + cost q' k bs
      | .advance => 1 + cost (true,none) (k+1) bs
      | .reset => 1 + (k+2) + cost (false,none) 0 bs

theorem cost_bound (q : ScanState) (k : Nat) (xs : List Bool) :
    cost q k xs ≤ 3*xs.length+k+1 := by
  induction xs generalizing q k with
  | nil => simp [cost]
  | cons b bs ih =>
    simp only [cost,List.length_cons]
    cases action q b with
    | keep q' => have h := ih q' k; dsimp only; omega
    | advance => have h := ih (true,none) (k+1); dsimp only; omega
    | reset => have h := ih (false,none) 0; dsimp only; omega

theorem unary_scan (v k mx : Nat) (rest : List Bool) (hk : k ≤ mx) :
    scan (true,none) k mx (doubleBits (List.replicate v true) ++ rest) =
      scan (true,none) (k+v) (max mx (k+v)) rest := by
  induction v generalizing k mx with
  | zero => simp [max_eq_left hk]
  | succ v ih =>
    simp only [List.replicate_succ,doubleBits_cons,List.cons_append,scan,action]
    simp only [↓reduceIte]
    rw [ih (k+1) (max mx (k+1)) (Nat.le_max_right _ _)]
    have he : max (max mx (k+1)) (k+1+v) = max mx (k+(v+1)) := by omega
    rw [he]
    congr 1
    omega

theorem literal_scan (l : Lit) (mx : Nat) (rest : List Bool) :
    scan (false,none) 0 mx (doubleBits l.encodeRaw ++ ([false,true] ++ rest)) =
      scan (false,none) 0 (max mx l.var) rest := by
  obtain ⟨s,v⟩ := l
  simp only [Lit.encodeRaw,Unary.encode,doubleBits_cons,List.cons_append]
  cases s <;> simp only [scan,action,Bool.false_eq_true,↓reduceIte]
  all_goals rw [unary_scan v 0 mx _ (Nat.zero_le _)]
  all_goals simp [scan,action]

theorem clause_scan (c : Clause) (mx : Nat) (rest : List Bool) :
    scan (false,none) 0 mx (c.encode ++ rest) =
      scan (false,none) 0 (max mx c.maxVar) rest := by
  induction c generalizing mx with
  | nil => simp
  | cons l c ih =>
    simp only [Clause.encode_cons,List.append_assoc,literal_scan,Clause.maxVar_cons]
    rw [ih]
    rw [Nat.max_assoc]

theorem formula_scan (φ : CNF) (mx : Nat) (rest : List Bool) :
    scan (false,none) 0 mx (φ.encode ++ rest) =
      scan (false,none) 0 (max mx φ.maxVar) rest := by
  induction φ generalizing mx with
  | nil => simp
  | cons c φ ih =>
    simp only [CNF.encode_cons,List.append_assoc,clause_scan,CNF.maxVar_cons]
    simp only [List.cons_append,List.nil_append,scan,action,Bool.true_eq_false,↓reduceIte]
    rw [ih]
    rw [Nat.max_assoc]

theorem decoded_maximum (xs : List Bool) (φ : CNF) (h : CNF.decode? xs = some φ) :
    scan (false,none) 0 0 xs = φ.maxVar := by
  have he := CNF.decode?_sound h
  subst xs
  have hm := formula_scan φ 0 []
  simpa [scan] using hm

end UnconstrainedPACDetection.FormulaMaximum

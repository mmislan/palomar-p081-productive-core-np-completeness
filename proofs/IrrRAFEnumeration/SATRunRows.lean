module

public import proofs.IrrRAFEnumeration.SATBitEncoding

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

/-- Three constant runs, with the true interval in the middle. -/
def spanRow (before count after : Nat) : List Bool :=
  List.replicate before false ++ List.replicate count true ++ List.replicate after false

theorem spanRow_length (a b c : Nat) : (spanRow a b c).length = a+b+c := by
  simp [spanRow]
  omega

theorem spanRow_getD (a b c i : Nat) :
    (spanRow a b c).getD i false = decide (a ≤ i ∧ i < a+b) := by
  simp only [spanRow, List.getD_eq_getElem?_getD, List.getElem?_append,
    List.length_append, List.length_replicate, List.getElem?_replicate]
  split_ifs <;> simp_all
  all_goals omega

/-- Two marked coordinates separated by zero runs; the first mark is optional. -/
def markedRow (before between after : Nat) (bit : Bool) : List Bool :=
  List.replicate before false ++ [bit] ++ List.replicate between false ++
    [true] ++ List.replicate after false

theorem markedRow_length (a b c : Nat) (bit : Bool) :
    (markedRow a b c bit).length = a+b+c+2 := by
  simp [markedRow]
  omega

theorem markedRow_getD (a b c i : Nat) (bit : Bool) :
    (markedRow a b c bit).getD i false =
      ((decide (i = a) && bit) || decide (i = a+b+1)) := by
  simp only [markedRow, List.getD_eq_getElem?_getD, List.getElem?_append,
    List.length_append, List.length_replicate, List.length_singleton,
    List.getElem?_replicate, List.getElem?_singleton]
  split_ifs <;> cases bit <;> simp_all <;> omega

/-- A finite incidence vector, in the exact molecule order used by sourceBits. -/
def moleculeRow {w q : Nat} (S : Finset (Molecule w q)) : List Bool :=
  List.ofFn (fun i : Fin (1+(w+(q+1))) => decide ((moleculeCode w q).symm i ∈ S))

theorem moleculeRow_length {w q : Nat} (S : Finset (Molecule w q)) :
    (moleculeRow S).length = 1+(w+(q+1)) := by simp [moleculeRow]; omega

theorem moleculeRow_getD {w q : Nat} (S : Finset (Molecule w q))
    (i : Fin (1+(w+(q+1)))) :
    (moleculeRow S).getD i.val false = decide ((moleculeCode w q).symm i ∈ S) := by
  simp only [moleculeRow, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  rw [dite_eq_left i.isLt]
  rfl

theorem eq_moleculeRow {w q : Nat} (S : Finset (Molecule w q)) (xs : List Bool)
    (hlen : xs.length = 1+(w+(q+1)))
    (hbit : ∀ i : Fin (1+(w+(q+1))), xs.getD i.val false =
      decide ((moleculeCode w q).symm i ∈ S)) : xs = moleculeRow S := by
  apply List.ext_getElem
  · rw [moleculeRow_length]
    exact hlen
  · intro i hi hj
    have h := hbit ⟨i, by omega⟩
    have h' := moleculeRow_getD S ⟨i, by omega⟩
    rw [← h'] at h
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hj, Option.getD_some] using h

theorem spanRow_singleton {w q : Nat} (x : Molecule w q) :
    spanRow (moleculeCode w q x).val 1
      (1+(w+(q+1))-(moleculeCode w q x).val-1) = moleculeRow {x} := by
  apply eq_moleculeRow
  · rw [spanRow_length]
    have hx := (moleculeCode w q x).isLt
    omega
  · intro i
    rw [spanRow_getD]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Finset.mem_singleton]
    rw [Equiv.symm_apply_eq]
    constructor
    · intro h; apply Fin.ext; omega
    · intro h; have hv := congrArg Fin.val h; omega

theorem markedRow_optional {w q : Nat} (x y : Molecule w q) (bit : Bool)
    (hxy : (moleculeCode w q x).val < (moleculeCode w q y).val) :
    markedRow (moleculeCode w q x).val
      ((moleculeCode w q y).val-(moleculeCode w q x).val-1)
      (1+(w+(q+1))-(moleculeCode w q y).val-1) bit =
      moleculeRow (insert y (if bit then {x} else ∅)) := by
  apply eq_moleculeRow
  · rw [markedRow_length]
    have hy := (moleculeCode w q y).isLt
    omega
  · intro i
    rw [markedRow_getD]
    have hp : (moleculeCode w q x).val+
        ((moleculeCode w q y).val-(moleculeCode w q x).val-1)+1 =
          (moleculeCode w q y).val := by omega
    rw [hp]
    apply Bool.eq_iff_iff.mpr
    cases bit <;> simp [Equiv.symm_apply_eq, Fin.ext_iff, or_comm]

end IrrRAFEnumeration.SATSource

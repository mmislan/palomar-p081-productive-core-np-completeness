module

public import proofs.IrrRAFEnumeration.SATRunRows

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

def signalMolecule {n m : Nat} (v : Wire n m) :
    Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m)) :=
  .wire (wireCode n m v)

def auxiliaryReaction {n m : Nat} (s : Step n m) :
    Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)) :=
  .inr (Fin.castSucc (stepCode n m s))

def wirePosition {n m : Nat} : Wire n m → Nat
  | .literal x => (choiceOffset n x).val+1
  | .covered i => 2*n+i.val+1
  | .clause j => 3*n+j.val+1
  | .output => 3*n+m+1

theorem moleculeCode_food (w q : Nat) :
    (moleculeCode w q .food).val = 0 := by
  simp [moleculeCode, moleculeEquiv, unitCode, finSumFinEquiv]

theorem moleculeCode_wire {w q : Nat} (v : Fin w) :
    (moleculeCode w q (.wire v)).val = 1+v.val := by
  simp [moleculeCode, moleculeEquiv, finSumFinEquiv]

theorem moleculeCode_marker {w q : Nat} (j : Fin (q+1)) :
    (moleculeCode w q (.marker j)).val = 1+w+j.val := by
  simp [moleculeCode, moleculeEquiv, finSumFinEquiv]
  omega

theorem signalMolecule_position {n m : Nat} (v : Wire n m) :
    (moleculeCode _ _ (signalMolecule v)).val = wirePosition v := by
  rw [signalMolecule, moleculeCode_wire]
  cases v <;> simp [wirePosition, wireCode, wireOffset, wireEquiv, unitCode, finSumFinEquiv]
  all_goals omega

theorem signal_before_marker {n m : Nat} (v : Wire n m)
    (j : Fin (Fintype.card (Step n m)+1)) :
    (moleculeCode _ _ (signalMolecule v)).val <
      (moleculeCode _ _ (Molecule.marker j :
        Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m)))).val := by
  rw [signalMolecule, moleculeCode_wire, moleculeCode_marker]
  have h := (wireCode n m v).isLt
  omega

def signalOutput {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    Step n m → Wire n m × Bool
  | .conflict _ => (.output,true)
  | .coverage x => (.covered x.1,true)
  | .clause j x => (.clause j,decide (x ∈ Φ j))
  | .finish => (.output,true)

theorem auxiliary_outputs {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (s : Step n m) :
    (crs (rules Φ)).outputs (auxiliaryReaction s) =
      insert (Molecule.marker (Fin.castSucc (stepCode n m s)))
        (if (signalOutput Φ s).2 then {signalMolecule (signalOutput Φ s).1} else ∅) := by
  cases s <;> simp [crs, rules, auxiliaryReaction, produces, signalOutput, signalMolecule]
  split_ifs <;> simp_all

/-- Product row for every signal rule: optional signal bit, then private marker. -/
def auxiliaryOutputRow {n m : Nat} (Φ : Fin m → Finset (Choice n)) (s : Step n m) :
    List Bool :=
  let p := wirePosition (signalOutput Φ s).1
  let h := 1+Fintype.card (Wire n m)+(stepCode n m s).val
  markedRow p (h-p-1) (moleculeCount n m-h-1) (signalOutput Φ s).2

theorem auxiliaryOutputRow_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (s : Step n m) :
    auxiliaryOutputRow Φ s = moleculeRow ((crs (rules Φ)).outputs (auxiliaryReaction s)) := by
  rw [auxiliary_outputs]
  have h := markedRow_optional (signalMolecule (signalOutput Φ s).1)
    (Molecule.marker (Fin.castSucc (stepCode n m s))) (signalOutput Φ s).2
    (signal_before_marker _ _)
  simpa only [signalMolecule_position, moleculeCode_marker, Fin.val_castSucc,
    auxiliaryOutputRow, moleculeCount] using h

theorem literal_input_row {n m : Nat} (Φ : Fin m → Finset (Choice n)) (x : Choice n) :
    spanRow 0 1 (moleculeCount n m-1) =
      moleculeRow ((crs (rules Φ)).inputs (.inl (inputCode n x))) := by
  have h := spanRow_singleton (Molecule.food :
    Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m)))
  simpa [moleculeCode_food, moleculeCount, crs] using h

theorem literal_output_row {n m : Nat} (Φ : Fin m → Finset (Choice n)) (x : Choice n) :
    spanRow (wirePosition (.literal (m := m) x)) 1
      (moleculeCount n m-wirePosition (.literal (m := m) x)-1) =
      moleculeRow ((crs (rules Φ)).outputs (.inl (inputCode n x))) := by
  have h := spanRow_singleton (signalMolecule (.literal (m := m) x))
  rw [signalMolecule_position] at h
  simpa [moleculeCount, crs, rules, signalMolecule] using h

theorem catalyst_row {n m : Nat}
    (r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))) :
    spanRow (1+Fintype.card (Wire n m)+(catalystIndex r).val) 1
      (moleculeCount n m-(1+Fintype.card (Wire n m)+(catalystIndex r).val)-1) =
      List.ofFn (fun i : Fin (moleculeCount n m) =>
        decide ((moleculeCode _ _).symm i = Molecule.marker (catalystIndex r))) := by
  have h := spanRow_singleton (Molecule.marker (catalystIndex r) :
    Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m)))
  simpa [moleculeCode_marker, moleculeCount, moleculeRow] using h

end IrrRAFEnumeration.SATSource

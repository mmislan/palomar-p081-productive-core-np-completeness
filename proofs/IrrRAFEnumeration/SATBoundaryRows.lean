module

public import proofs.IrrRAFEnumeration.SATReactionRows

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource

theorem spanRow_of_membership {w q : Nat} (S : Finset (Molecule w q)) (a b c : Nat)
    (hlen : a+b+c = 1+(w+(q+1)))
    (h : ∀ x, x ∈ S ↔ a ≤ (moleculeCode w q x).val ∧
      (moleculeCode w q x).val < a+b) : spanRow a b c = moleculeRow S := by
  apply eq_moleculeRow
  · simpa [spanRow_length] using hlen
  · intro i
    rw [spanRow_getD]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq, Equiv.apply_symm_apply] using
      (h ((moleculeCode w q).symm i)).symm

def blockLastRow (a b c : Nat) : List Bool := spanRow a b c ++ [true]

theorem blockLastRow_getD (a b c i : Nat) :
    (blockLastRow a b c).getD i false = decide ((a ≤ i ∧ i < a+b) ∨ i = a+b+c) := by
  by_cases hi : i < a+b+c
  · have hget : (blockLastRow a b c).getD i false = (spanRow a b c).getD i false := by
      simp only [blockLastRow, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by simpa [spanRow_length] using hi)]
    rw [hget, spanRow_getD]
    have hn : i ≠ a+b+c := by omega
    simp [hn]
  · simp only [blockLastRow, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by simp [spanRow_length]; omega)]
    simp only [spanRow_length, List.getElem?_singleton]
    split_ifs <;> simp_all
    all_goals omega

theorem blockLastRow_of_membership {w q : Nat} (S : Finset (Molecule w q)) (a b c : Nat)
    (hlen : a+b+c+1 = 1+(w+(q+1)))
    (h : ∀ x, x ∈ S ↔ (a ≤ (moleculeCode w q x).val ∧
      (moleculeCode w q x).val < a+b) ∨ (moleculeCode w q x).val = a+b+c) :
    blockLastRow a b c = moleculeRow S := by
  apply eq_moleculeRow
  · simpa [blockLastRow, spanRow_length] using hlen
  · intro i
    rw [blockLastRow_getD]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq, Equiv.apply_symm_apply] using
      (h ((moleculeCode w q).symm i)).symm

def finishInputs (n m : Nat) :
    Finset (Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m))) :=
  Finset.univ.image (fun i : Fin n => signalMolecule (Wire.covered i)) ∪
    Finset.univ.image (fun j : Fin m => signalMolecule (Wire.clause j))

theorem finish_inputs_eq {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    (crs (rules Φ)).inputs (auxiliaryReaction (Step.finish (n := n) (m := m))) =
      finishInputs n m := by
  simp [crs, rules, auxiliaryReaction, needs, finishInputs, signalMolecule,
    Finset.image_union, Finset.image_image, Function.comp_def]

theorem code_wireSignal {n m : Nat} (v : Wire n m) :
    (moleculeCode (Fintype.card (Wire n m)) (Fintype.card (Step n m))
      (.wire (wireCode n m v))).val = wirePosition v := signalMolecule_position v

theorem finish_input_row {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    spanRow (2*n+1) (n+m) (moleculeCount n m-(3*n+m+1)) =
      moleculeRow ((crs (rules Φ)).inputs (auxiliaryReaction (Step.finish (n := n) (m := m)))) := by
  rw [finish_inputs_eq]
  apply spanRow_of_membership
  · simp only [moleculeCount, wire_card, step_card]
    omega
  · intro x
    cases x with
    | food =>
        simp [finishInputs, signalMolecule, moleculeCode_food]
    | marker j =>
        simp [finishInputs, signalMolecule, moleculeCode_marker, wire_card]
        omega
    | wire k =>
        obtain ⟨v,rfl⟩ := (wireCode n m).surjective k
        rw [code_wireSignal]
        cases v with
        | literal x =>
            have hx := (choiceOffset n x).isLt
            simp [finishInputs, signalMolecule, Finset.mem_image, wirePosition]
            all_goals omega
        | covered i =>
            have hi := i.isLt
            simp [finishInputs, signalMolecule, Finset.mem_image, wirePosition]
            all_goals omega
        | clause j =>
            have hj := j.isLt
            simp [finishInputs, signalMolecule, Finset.mem_image, wirePosition]
            all_goals omega
        | output =>
            simp [finishInputs, signalMolecule, Finset.mem_image, wirePosition]
            omega

theorem reset_input_row {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    spanRow (3*n+m+1) 1 (moleculeCount n m-(3*n+m+1)-1) =
      moleculeRow ((crs (rules Φ)).inputs (reset (n := Fintype.card (Choice n))
        (q := Fintype.card (Step n m)))) := by
  have h := spanRow_singleton (signalMolecule (Wire.output (n := n) (m := m)))
  rw [signalMolecule_position] at h
  simpa [wirePosition, moleculeCount, reset, crs, rules, signalMolecule] using h

theorem reset_output_row {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    blockLastRow 1 (Fintype.card (Wire n m)) (Fintype.card (Step n m)) =
      moleculeRow ((crs (rules Φ)).outputs (reset (n := Fintype.card (Choice n))
        (q := Fintype.card (Step n m)))) := by
  apply blockLastRow_of_membership
  · omega
  · intro x
    cases x with
    | food =>
        simp [reset, crs, moleculeCode_food]
        omega
    | wire v =>
        have hv := v.isLt
        simp [reset, crs, moleculeCode_wire]
    | marker j =>
        have hj := j.isLt
        simp [reset, crs, moleculeCode_marker, Fin.ext_iff]

end IrrRAFEnumeration.SATSource

module

public import proofs.IrrRAFEnumeration.ExpectedQueryLength

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

theorem input_cell_blank_iff (z : List Bool) (i : Nat) :
    (parkedInput z).cells (i+1) = Γ.blank ↔ z.length ≤ i := by
  by_cases h : i < z.length
  · change (Tape.init (z.map Γ.ofBool)).cells (i+1) = Γ.blank ↔ _
    rw [Tape.init_ofBool_cells_lt z i h]
    cases hb : z[i] <;> simp [Γ.ofBool, Nat.not_le_of_gt h]
  · have hi : z.length ≤ i := by omega
    change (Tape.init (z.map Γ.ofBool)).cells (i+1) = Γ.blank ↔ _
    rw [Tape.init_ofBool_cells_ge z i hi]
    simp [hi]

theorem input_boundary_iff (z : List Bool) (m : Nat) (hm : 0 < m) :
    ((parkedInput z).cells m ≠ Γ.blank ∧
      (parkedInput z).cells (m+1) = Γ.blank) ↔ z.length = m := by
  obtain ⟨i, rfl⟩ : ∃ i, m = i+1 := ⟨m-1, by omega⟩
  simp only [ne_eq, input_cell_blank_iff]
  omega

def nonblankIndex (s : Γ) : Fin 4 := if s = Γ.blank then 0 else 1
def blankIndex (s : Γ) : Fin 4 := if s = Γ.blank then 1 else 0

def boundaryProbeTM {k : Nat} (pos left right : Fin k) : TM k :=
  seqTM (symProbeTM nonblankIndex pos left)
    (seqTM (incRegTM pos) (symProbeTM blankIndex pos right))

def boundaryWork {k : Nat} (work : Fin k → Tape) (pos left right : Fin k)
    (inp : Tape) (m : Nat) : Fin k → Tape :=
  Function.update
    (Function.update
      (Function.update work left (regTape (nonblankIndex (inp.cells m)).val))
      pos (regTape (m+1)))
    right (regTape (blankIndex (inp.cells (m+1))).val)

theorem boundaryProbeTM_correct {k : Nat} (pos left right : Fin k)
    (hpl : pos ≠ left) (hpr : pos ≠ right) (hlr : left ≠ right)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool) (m : Nat)
    (hp : Parked inp) (hh : inp.head = 1) (hs : inp.cells 0 = Γ.start)
    (hw : ∀ i, Parked (work i)) (hm : work pos = regTape m)
    (hl : work left = regTape 0) (hr : work right = regTape 0) :
    (boundaryProbeTM pos left right).HoareTime
      (EmitPred inp work ys)
      (EmitPred inp (boundaryWork work pos left right inp m) ys)
      (8*m+49) := by
  let W1 := Function.update work left (regTape (nonblankIndex (inp.cells m)).val)
  let W2 := Function.update W1 pos (regTape (m+1))
  have hw1 : ∀ i, Parked (W1 i) := updateReg_parked work hw left _
  have hw2 : ∀ i, Parked (W2 i) := updateReg_parked W1 hw1 pos _
  have h1 := symProbeTM_hoareTime nonblankIndex pos left hpl m 0 inp work ys
    hp hh hs hw hm hl
  simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] at h1
  have h2 := incRegTM_hoareTime pos m inp W1 ys hp (fun i _ => hw1 i)
    (by simpa [W1, Function.update_of_ne hpl] using hm)
  have h3 := symProbeTM_hoareTime blankIndex pos right hpr (m+1) 0 inp W2 ys
    hp hh hs hw2 (by simp [W2])
    (by simpa [W2, W1, Function.update_of_ne hpr.symm,
      Function.update_of_ne hlr.symm] using hr)
  simp only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] at h3
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hp hw2 ys) h3
  have hall := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw1 ys) h23
  dsimp only [W1, W2] at hall
  unfold boundaryWork
  convert hall using 1
  · rfl
  · omega

theorem boundary_flags_iff (z : List Bool) (m : Nat) (hm : 0 < m) :
    ((nonblankIndex ((parkedInput z).cells m)).val = 1 ∧
      (blankIndex ((parkedInput z).cells (m+1))).val = 1) ↔ z.length = m := by
  have h := input_boundary_iff z m hm
  by_cases h1 : (parkedInput z).cells m = Γ.blank <;>
    by_cases h2 : (parkedInput z).cells (m+1) = Γ.blank <;>
    simpa [nonblankIndex, blankIndex, h1, h2] using h

theorem expected_boundary_iff (z : List Bool) :
    let m := expectedLength (parse z).knownCount (parse z).moleculeCount
      (parse z).reactionCount
    ((nonblankIndex ((parkedInput z).cells m)).val = 1 ∧
      (blankIndex ((parkedInput z).cells (m+1))).val = 1) ↔ SizeCheck z := by
  dsimp only
  rw [boundary_flags_iff z _ (by unfold expectedLength; omega)]
  rw [expectedLength_parse]
  rfl

theorem boundaryWork_reads_iff {k : Nat} (work : Fin k → Tape)
    (pos left right : Fin k) (hpl : pos ≠ left) (hlr : left ≠ right)
    (z : List Bool) (m : Nat) (hm : 0 < m) :
    let w := boundaryWork work pos left right (parkedInput z) m
    ((w left).read = Γ.one ∧ (w right).read = Γ.one) ↔ z.length = m := by
  have h := boundary_flags_iff z m hm
  by_cases h1 : (parkedInput z).cells m = Γ.blank <;>
    by_cases h2 : (parkedInput z).cells (m+1) = Γ.blank <;>
    simpa [boundaryWork, Function.update_of_ne hlr,
      Function.update_of_ne hpl.symm, nonblankIndex, blankIndex,
      h1, h2, Tape.read, regTape, regCells] using h

theorem queryProbeTM_correct {k : Nat} (pos left right : Fin k)
    (hpl : pos ≠ left) (hpr : pos ≠ right) (hlr : left ≠ right)
    (z : List Bool) (work : Fin k → Tape) (ys : List Bool)
    (hw : ∀ i, Parked (work i))
    (hm : work pos = regTape (expectedLength (parse z).knownCount
      (parse z).moleculeCount (parse z).reactionCount))
    (hl : work left = regTape 0) (hr : work right = regTape 0) :
    let m := expectedLength (parse z).knownCount (parse z).moleculeCount
      (parse z).reactionCount
    (boundaryProbeTM pos left right).HoareTime
      (EmitPred (parkedInput z) work ys)
      (fun inp w out =>
        EmitPred (parkedInput z) (boundaryWork work pos left right (parkedInput z) m)
          ys inp w out ∧
        ((w left).read = Γ.one ∧ (w right).read = Γ.one ↔ SizeCheck z))
      (8*m+49) := by
  dsimp only
  apply (boundaryProbeTM_correct pos left right hpl hpr hlr (parkedInput z) work ys _
    (parkedInput_parked z) rfl (by simp [parkedInput]) hw hm hl hr).strengthen_post
  intro inp w out h
  refine ⟨h, ?_⟩
  rcases h with ⟨_, rfl, _⟩
  have hb := boundaryWork_reads_iff work pos left right hpl hlr z
    (expectedLength (parse z).knownCount (parse z).moleculeCount (parse z).reactionCount)
    (by unfold expectedLength; omega)
  dsimp only at hb
  apply hb.trans
  rw [expectedLength_parse]
  rfl

end IrrRAFEnumeration.CompletionQuery

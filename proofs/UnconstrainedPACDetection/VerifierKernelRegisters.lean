module

public import proofs.UnconstrainedPACDetection.VerifierWitnessPlacement
public import proofs.Complexitylib.Models.TuringMachine.Registers.DecReg

@[expose] public section

namespace UnconstrainedPACDetection.VerifierKernelRegisters
open Complexity Complexity.TM

private theorem updateReg_parked (work : Fin 30 → Tape) (hw : ∀ j, Parked (work j))
    (i : Fin 30) (v : Nat) : ∀ j, Parked (Function.update work i (regTape v) j) := by
  intro j
  by_cases hj : j = i
  · subst j; simpa using parked_regTape v
  · simpa only [Function.update_of_ne hj] using hw j

def machine : TM 30 :=
  seqTM (copyIntoTM (23 : Fin 30) 9)
  (seqTM (decRegTM (9 : Fin 30))
  (seqTM (copyIntoTM (26 : Fin 30) 10)
  (seqTM (decRegTM (10 : Fin 30))
  (seqTM (copyIntoTM (23 : Fin 30) 13)
  (seqTM (copyIntoTM (26 : Fin 30) 16)
  (seqTM (addIntoTM (26 : Fin 30) 16)
  (seqTM (setConstTM (1 : Fin 30) 1) (setConstTM (12 : Fin 30) 2))))))))

def finalWork (work : Fin 30 → Tape) (m n : Nat) :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update work 9 (regTape (m-1))) 10 (regTape (n-1)))
      13 (regTape m)) 16 (regTape (2*n))) 1 (regTape 1)) 12 (regTape 2)

theorem registers_hoare (m n : Nat) (inp : Tape) (work : Fin 30 → Tape)
    (hi : Parked inp) (hw : ∀ j, Parked (work j))
    (hm : work 23 = regTape m) (hn : work 26 = regTape n)
    (hz : ∀ j : Fin 30, j = 1 ∨ j = 9 ∨ j = 10 ∨ j = 12 ∨ j = 13 ∨ j = 16 →
      work j = regTape 0) :
    machine.HoareTime (EmitPred inp work []) (EmitPred inp (finalWork work m n) [])
      (100*(m+n+1)^2) := by
  let W1 := Function.update work 9 (regTape m)
  let W2 := Function.update W1 9 (regTape (m-1))
  let W3 := Function.update W2 10 (regTape n)
  let W4 := Function.update W3 10 (regTape (n-1))
  let W5 := Function.update W4 13 (regTape m)
  let W6 := Function.update W5 16 (regTape n)
  let W7 := Function.update W6 16 (regTape (n+n))
  let W8 := Function.update W7 1 (regTape 1)
  have hp1 := updateReg_parked work hw 9 m
  have hp2 := updateReg_parked W1 hp1 9 (m-1)
  have hp3 := updateReg_parked W2 hp2 10 n
  have hp4 := updateReg_parked W3 hp3 10 (n-1)
  have hp5 := updateReg_parked W4 hp4 13 m
  have hp6 := updateReg_parked W5 hp5 16 n
  have hp7 := updateReg_parked W6 hp6 16 (n+n)
  have hp8 := updateReg_parked W7 hp7 1 1
  have h1 := copyIntoTM_hoareTime (23 : Fin 30) 9 (by decide) m 0 inp work [] hi
    (fun j _ => hw j) hm (hz 9 (by simp))
  have h2 := decRegTM_hoareTime (9 : Fin 30) m inp W1 [] hi (fun j _ => hp1 j) rfl
  have h3 := copyIntoTM_hoareTime (26 : Fin 30) 10 (by decide) n 0 inp W2 [] hi
    (fun j _ => hp2 j) (by simpa [W2,W1] using hn) (by simpa [W2,W1] using hz 10 (by simp))
  have h4 := decRegTM_hoareTime (10 : Fin 30) n inp W3 [] hi (fun j _ => hp3 j) rfl
  have h5 := copyIntoTM_hoareTime (23 : Fin 30) 13 (by decide) m 0 inp W4 [] hi
    (fun j _ => hp4 j) (by simpa [W4,W3,W2,W1] using hm)
    (by simpa [W4,W3,W2,W1] using hz 13 (by simp))
  have h6 := copyIntoTM_hoareTime (26 : Fin 30) 16 (by decide) n 0 inp W5 [] hi
    (fun j _ => hp5 j) (by simpa [W5,W4,W3,W2,W1] using hn)
    (by simpa [W5,W4,W3,W2,W1] using hz 16 (by simp))
  have h7 := addIntoTM_hoareTime (26 : Fin 30) 16 (by decide) n n inp W6 [] hi
    (fun j _ => hp6 j) (by simpa [W6,W5,W4,W3,W2,W1] using hn) rfl
  have h8 := setConstTM_hoareTime (1 : Fin 30) 1 0 inp W7 [] hi hp7
    (by simpa [W7,W6,W5,W4,W3,W2,W1] using hz 1 (by simp))
  have h9 := setConstTM_hoareTime (12 : Fin 30) 2 0 inp W8 [] hi hp8
    (by simpa [W8,W7,W6,W5,W4,W3,W2,W1] using hz 12 (by simp))
  have h89 := seqTM_hoareTime _ _ h8 (emitPred_transition hi hp8 []) h9
  have h789 := seqTM_hoareTime _ _ h7 (emitPred_transition hi hp7 []) h89
  have h6789 := seqTM_hoareTime _ _ h6 (emitPred_transition hi hp6 []) h789
  have h56789 := seqTM_hoareTime _ _ h5 (emitPred_transition hi hp5 []) h6789
  have h456789 := seqTM_hoareTime _ _ h4 (emitPred_transition hi hp4 []) h56789
  have h3456789 := seqTM_hoareTime _ _ h3 (emitPred_transition hi hp3 []) h456789
  have h23456789 := seqTM_hoareTime _ _ h2 (emitPred_transition hi hp2 []) h3456789
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hi hp1 []) h23456789
  have he : Function.update W8 12 (regTape 2) = finalWork work m n := by
    simp [W8,W7,W6,W5,W4,W3,W2,W1,finalWork,two_mul]
  rw [he] at h
  exact h.mono_bound (by nlinarith)

end UnconstrainedPACDetection.VerifierKernelRegisters

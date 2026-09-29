module

public import proofs.UnconstrainedPACDetection.FormulaHeaderCount
public import proofs.Complexitylib.Models.TuringMachine.Registers.Horner

@[expose] public section

namespace UnconstrainedPACDetection.FormulaHeaderRegisters
open Complexity Complexity.TM

def value (o v : Nat) : Nat := 31 + 34*o + 6*v + 2*o*v
def bank (work : Fin 5 → Tape) (d : Nat) : Fin 5 → Tape :=
  Function.update work 4 (regTape d)

theorem bank_parked (work : Fin 5 → Tape) (hp : ∀ i, Parked (work i)) (d : Nat) :
    ∀ i, Parked (bank work d i) := by
  intro i
  by_cases hi : i = 4
  · subst i; simp only [bank,Function.update_self]; exact parked_regTape _
  · simpa only [bank,Function.update_of_ne hi] using hp i

private theorem repeat_hoare (m : TM 5) (q M B : Nat) (inp : Tape)
    (work : Fin 5 → Tape) (ys : List Bool) (hi : Parked inp) (hp : ∀ i, Parked (work i))
    (step : ∀ d, d+q ≤ M → m.HoareTime
      (EmitPred inp (bank work d) ys) (EmitPred inp (bank work (d+q)) ys) B)
    (k d : Nat) (hd : d+k*q ≤ M) : (iterTM m k).HoareTime
      (EmitPred inp (bank work d) ys) (EmitPred inp (bank work (d+k*q)) ys)
      (k*(B+1)+1) := by
  induction k generalizing d with
  | zero => simpa [iterTM] using skipTM_hoareTime inp (bank work d) ys hi (bank_parked work hp d)
  | succ k ih =>
    have hs := step d (by nlinarith)
    have hr := ih (d+q) (by nlinarith)
    have h := seqTM_hoareTime _ _ hs
      (emitPred_transition hi (bank_parked work hp (d+q)) ys) hr
    have he : d+q+k*q = d+(k+1)*q := by ring
    rw [he] at h
    exact h.mono_bound (by nlinarith)

private theorem add_step (src : Fin 5) (hs : src ≠ 4) (a M d : Nat)
    (inp : Tape) (work : Fin 5 → Tape) (ys : List Bool)
    (hi : Parked inp) (hp : ∀ i, Parked (work i)) (ha : work src = regTape a)
    (ham : a ≤ M) (hd : d+a ≤ M) : (addIntoTM src 4).HoareTime
      (EmitPred inp (bank work d) ys) (EmitPred inp (bank work (d+a)) ys) (opBudget M) := by
  have h := addIntoTM_hoareTime src 4 hs a d inp (bank work d) ys hi
    (fun i _ => bank_parked work hp d i)
    (by simpa [bank,hs] using ha) (by simp [bank])
  have hb := h.mono_bound (addIntoTM_le_opBudget ham hd)
  simpa only [bank,Function.update_idem] using hb

private theorem product_step (a b M d : Nat) (inp : Tape) (work : Fin 5 → Tape)
    (ys : List Bool) (hi : Parked inp) (hp : ∀ i, Parked (work i))
    (ha : work 1 = regTape a) (hb : work 2 = regTape b)
    (ham : a ≤ M) (hbm : b ≤ M) (hd : d+a*b ≤ M) :
    (mulAddIntoTM (1 : Fin 5) 2 4).HoareTime
      (EmitPred inp (bank work d) ys) (EmitPred inp (bank work (d+a*b)) ys) (opBudget M) := by
  have h := mulAddIntoTM_hoareTime (1 : Fin 5) 2 4 (by decide) (by decide) (by decide)
    a b d inp (bank work d) ys hi (fun i _ => bank_parked work hp d i)
    (by simpa [bank] using ha) (by simpa [bank] using hb) (by simp [bank])
  have ht := h.mono_bound (mulAddIntoTM_le_opBudget ham hbm hd)
  simpa only [bank,Function.update_idem] using ht

def machine : TM 5 := seqTM (setConstTM 4 31)
  (seqTM (iterTM (addIntoTM 1 4) 34)
    (seqTM (iterTM (addIntoTM 2 4) 6) (iterTM (mulAddIntoTM 1 2 4) 2)))

/-- Actual fixed-register program; all other tapes and the output prefix are preserved. -/
theorem arithmetic_hoare (a b M : Nat) (inp : Tape) (work : Fin 5 → Tape)
    (ys : List Bool) (hi : Parked inp) (hp : ∀ i, Parked (work i))
    (ha : work 1 = regTape a) (hb : work 2 = regTape b) (h0 : work 4 = regTape 0)
    (ham : a ≤ M) (hbm : b ≤ M) (hv : value a b ≤ M) :
    machine.HoareTime (EmitPred inp work ys) (EmitPred inp (bank work (value a b)) ys)
      (50*(opBudget M+1)) := by
  have h31 : 31 ≤ M := by unfold value at hv; omega
  have hinit := (setConstTM_hoareTime (4 : Fin 5) 31 0 inp work ys hi hp h0).mono_bound
    (setConstTM_le_opBudget h31 (Nat.zero_le M))
  have hA := repeat_hoare (addIntoTM (1 : Fin 5) 4) a M (opBudget M) inp work ys hi hp
    (fun d hd => add_step 1 (by decide) a M d inp work ys hi hp ha ham hd) 34 31
    (by unfold value at hv; nlinarith)
  have hB := repeat_hoare (addIntoTM (2 : Fin 5) 4) b M (opBudget M) inp work ys hi hp
    (fun d hd => add_step 2 (by decide) b M d inp work ys hi hp hb hbm hd) 6 (31+34*a)
    (by unfold value at hv; nlinarith)
  have hP := repeat_hoare (mulAddIntoTM (1 : Fin 5) 2 4) (a*b) M (opBudget M) inp work ys hi hp
    (fun d hd => product_step a b M d inp work ys hi hp ha hb ham hbm hd) 2 (31+34*a+6*b)
    (by simpa [value,Nat.mul_assoc] using hv)
  have hBP := seqTM_hoareTime _ _ hB
    (emitPred_transition hi (bank_parked work hp _) ys) hP
  have hABP := seqTM_hoareTime _ _ hA
    (emitPred_transition hi (bank_parked work hp _) ys) hBP
  have h := seqTM_hoareTime _ _ hinit
    (emitPred_transition hi (bank_parked work hp 31) ys) hABP
  have he : 31+34*a+6*b+2*(a*b) = value a b := by unfold value; ring
  rw [he] at h
  exact h.mono_bound (by omega)

theorem value_bound (N a b : Nat) (ha : a ≤ N+1) (hb : b ≤ 3*N+2) :
    value a b ≤ 128*(N+1)^2 := by
  have hp := Nat.mul_le_mul ha hb
  unfold value
  nlinarith

/-- Semantic consumer of the register value: it is the existing source's entity header. -/
theorem formula_value (φ : SAT.CNF) :
    value (FormulaWiring.occurrences φ).length (FormulaWiring.varCount φ) =
      (FormulaPACEncoding.table φ).entities :=
  (FormulaHeaderCount.table_entities_from_counts φ).symm

end UnconstrainedPACDetection.FormulaHeaderRegisters

module

public import proofs.UnconstrainedPACDetection.FormulaReactionCount
public import proofs.Complexitylib.Models.TuringMachine.Registers.Horner

@[expose] public section

namespace UnconstrainedPACDetection.FormulaReactionRegisters
open Complexity Complexity.TM

def value (c o v : Nat) : Nat := 20+c+20*o+5*v+2*o*v
def bank (work : Fin 7 → Tape) (d : Nat) : Fin 7 → Tape :=
  Function.update work 5 (regTape d)

theorem bank_parked (work : Fin 7 → Tape) (hp : ∀ i, Parked (work i)) (d : Nat) :
    ∀ i, Parked (bank work d i) := by
  intro i
  by_cases hi : i = 5
  · subst i; simp only [bank,Function.update_self]; exact parked_regTape _
  · simpa only [bank,Function.update_of_ne hi] using hp i

private theorem repeat_hoare (m : TM 7) (q M B : Nat) (inp : Tape)
    (work : Fin 7 → Tape) (ys : List Bool) (hi : Parked inp) (hp : ∀ i, Parked (work i))
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

private theorem add_step (src : Fin 7) (hs : src ≠ 5) (a M d : Nat)
    (inp : Tape) (work : Fin 7 → Tape) (ys : List Bool)
    (hi : Parked inp) (hp : ∀ i, Parked (work i)) (ha : work src = regTape a)
    (ham : a ≤ M) (hd : d+a ≤ M) : (addIntoTM src 5).HoareTime
      (EmitPred inp (bank work d) ys) (EmitPred inp (bank work (d+a)) ys) (opBudget M) := by
  have h := addIntoTM_hoareTime src 5 hs a d inp (bank work d) ys hi
    (fun i _ => bank_parked work hp d i)
    (by simpa [bank,hs] using ha) (by simp [bank])
  have hb := h.mono_bound (addIntoTM_le_opBudget ham hd)
  simpa only [bank,Function.update_idem] using hb

private theorem product_step (a b M d : Nat) (inp : Tape) (work : Fin 7 → Tape)
    (ys : List Bool) (hi : Parked inp) (hp : ∀ i, Parked (work i))
    (ha : work 1 = regTape a) (hb : work 2 = regTape b)
    (ham : a ≤ M) (hbm : b ≤ M) (hd : d+a*b ≤ M) :
    (mulAddIntoTM (1 : Fin 7) 2 5).HoareTime
      (EmitPred inp (bank work d) ys) (EmitPred inp (bank work (d+a*b)) ys) (opBudget M) := by
  have h := mulAddIntoTM_hoareTime (1 : Fin 7) 2 5 (by decide) (by decide) (by decide)
    a b d inp (bank work d) ys hi (fun i _ => bank_parked work hp d i)
    (by simpa [bank] using ha) (by simpa [bank] using hb) (by simp [bank])
  have ht := h.mono_bound (mulAddIntoTM_le_opBudget ham hbm hd)
  simpa only [bank,Function.update_idem] using ht

def machine : TM 7 := seqTM (setConstTM 5 20)
  (seqTM (addIntoTM 0 5) (seqTM (iterTM (addIntoTM 1 5) 20)
    (seqTM (iterTM (addIntoTM 2 5) 5) (iterTM (mulAddIntoTM 1 2 5) 2))))

theorem arithmetic_hoare (c a b M : Nat) (inp : Tape) (work : Fin 7 → Tape)
    (ys : List Bool) (hi : Parked inp) (hp : ∀ i, Parked (work i))
    (hc : work 0 = regTape c) (ha : work 1 = regTape a) (hb : work 2 = regTape b)
    (h5 : work 5 = regTape 1) (hcm : c ≤ M) (ham : a ≤ M) (hbm : b ≤ M)
    (hv : value c a b ≤ M) :
    machine.HoareTime (EmitPred inp work ys)
      (EmitPred inp (bank work (value c a b)) ys) (40*(opBudget M+1)) := by
  have h20 : 20 ≤ M := by unfold value at hv; omega
  have hinit := (setConstTM_hoareTime (5 : Fin 7) 20 1 inp work ys hi hp h5).mono_bound
    (setConstTM_le_opBudget h20 (by omega))
  have hC := add_step 0 (by decide) c M 20 inp work ys hi hp hc hcm
    (by unfold value at hv; nlinarith)
  have hA := repeat_hoare (addIntoTM (1 : Fin 7) 5) a M (opBudget M) inp work ys hi hp
    (fun d hd => add_step 1 (by decide) a M d inp work ys hi hp ha ham hd) 20 (20+c)
    (by unfold value at hv; nlinarith)
  have hB := repeat_hoare (addIntoTM (2 : Fin 7) 5) b M (opBudget M) inp work ys hi hp
    (fun d hd => add_step 2 (by decide) b M d inp work ys hi hp hb hbm hd) 5 (20+c+20*a)
    (by unfold value at hv; nlinarith)
  have hP := repeat_hoare (mulAddIntoTM (1 : Fin 7) 2 5) (a*b) M (opBudget M) inp work ys hi hp
    (fun d hd => product_step a b M d inp work ys hi hp ha hb ham hbm hd) 2 (20+c+20*a+5*b)
    (by simpa [value,Nat.mul_assoc] using hv)
  have hBP := seqTM_hoareTime _ _ hB (emitPred_transition hi (bank_parked work hp _) ys) hP
  have hABP := seqTM_hoareTime _ _ hA (emitPred_transition hi (bank_parked work hp _) ys) hBP
  have hCABP := seqTM_hoareTime _ _ hC (emitPred_transition hi (bank_parked work hp _) ys) hABP
  have h := seqTM_hoareTime _ _ hinit (emitPred_transition hi (bank_parked work hp _) ys) hCABP
  have he : 20+c+20*a+5*b+2*(a*b) = value c a b := by unfold value; ring
  rw [he] at h
  exact h.mono_bound (by omega)

theorem value_bound (n c o v : Nat) (hc : c ≤ n+1) (ho : o ≤ n+1) (hv : v ≤ 3*n+2) :
    value c o v ≤ 128*(n+1)^2 := by
  have hp := Nat.mul_le_mul ho hv
  unfold value
  nlinarith

theorem formula_value (φ : Complexity.SAT.CNF) :
    value φ.length (FormulaWiring.occurrences φ).length (FormulaWiring.varCount φ) =
      (FormulaPACEncoding.table φ).reactions := by
  rw [FormulaReactionCount.table_reactions_from_counts]
  unfold value
  ring

end UnconstrainedPACDetection.FormulaReactionRegisters

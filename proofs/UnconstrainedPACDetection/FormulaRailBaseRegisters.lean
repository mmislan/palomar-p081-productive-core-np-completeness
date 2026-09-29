module

public import proofs.UnconstrainedPACDetection.FormulaRailBase
public import proofs.Complexitylib.Models.TuringMachine.Registers.Horner

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailBaseRegisters
open Complexity Complexity.TM

def bit (s : Bool) : Nat := if s then 1 else 0
def bank (work : Fin 17 → Tape) (d : Nat) : Fin 17 → Tape :=
  Function.update work 11 (regTape d)

theorem parked (work : Fin 17 → Tape) (hp : ∀ i, Parked (work i)) (d : Nat) :
    ∀ i, Parked (bank work d i) := by
  intro i
  by_cases hi : i = 11
  · subst i; simp only [bank,Function.update_self]; exact parked_regTape _
  · simpa only [bank,Function.update_of_ne hi] using hp i

private theorem repeat_hoare (m : TM 17) (q M B : Nat) (inp : Tape)
    (work : Fin 17 → Tape) (ys : List Bool) (hi : Parked inp) (hp : ∀ i, Parked (work i))
    (step : ∀ d, d+q ≤ M → m.HoareTime
      (EmitPred inp (bank work d) ys) (EmitPred inp (bank work (d+q)) ys) B)
    (k d : Nat) (hd : d+k*q ≤ M) : (iterTM m k).HoareTime
      (EmitPred inp (bank work d) ys) (EmitPred inp (bank work (d+k*q)) ys)
      (k*(B+1)+1) := by
  induction k generalizing d with
  | zero => simpa [iterTM] using skipTM_hoareTime inp (bank work d) ys hi (parked work hp d)
  | succ k ih =>
    have hs := step d (by nlinarith)
    have hr := ih (d+q) (by nlinarith)
    have h := seqTM_hoareTime _ _ hs (emitPred_transition hi (parked work hp (d+q)) ys) hr
    have he : d+q+k*q = d+(k+1)*q := by ring
    rw [he] at h
    exact h.mono_bound (by nlinarith)

private theorem add_step (src : Fin 17) (hs : src ≠ 11) (a M d : Nat)
    (inp : Tape) (work : Fin 17 → Tape) (ys : List Bool)
    (hi : Parked inp) (hp : ∀ i, Parked (work i)) (ha : work src = regTape a)
    (ham : a ≤ M) (hd : d+a ≤ M) : (addIntoTM src 11).HoareTime
      (EmitPred inp (bank work d) ys) (EmitPred inp (bank work (d+a)) ys) (opBudget M) := by
  have h := addIntoTM_hoareTime src 11 hs a d inp (bank work d) ys hi
    (fun i _ => parked work hp d i) (by simpa [bank,hs] using ha) (by simp [bank])
  simpa only [bank,Function.update_idem] using h.mono_bound (addIntoTM_le_opBudget ham hd)

private theorem product_step (L v M d : Nat) (inp : Tape) (work : Fin 17 → Tape)
    (ys : List Bool) (hi : Parked inp) (hp : ∀ i, Parked (work i))
    (hL : work 15 = regTape L) (hv : work 5 = regTape v)
    (hLm : L ≤ M) (hvm : v ≤ M) (hd : d+L*v ≤ M) :
    (mulAddIntoTM (15 : Fin 17) 5 11).HoareTime
      (EmitPred inp (bank work d) ys) (EmitPred inp (bank work (d+L*v)) ys) (opBudget M) := by
  have h := mulAddIntoTM_hoareTime (15 : Fin 17) 5 11 (by decide) (by decide) (by decide)
    L v d inp (bank work d) ys hi (fun i _ => parked work hp d i)
    (by simpa [bank] using hL) (by simpa [bank] using hv) (by simp [bank])
  simpa only [bank,Function.update_idem] using h.mono_bound (mulAddIntoTM_le_opBudget hLm hvm hd)

def machine (s : Bool) : TM 17 := seqTM (setConstTM 11 (1+bit s))
  (seqTM (addIntoTM 16 11) (seqTM (iterTM (addIntoTM 15 11) (20+bit s))
    (seqTM (iterTM (addIntoTM 5 11) 2) (iterTM (mulAddIntoTM 15 5 11) 2))))

/-- Compute the actual canonical head offset from live dimensions and variable.
    Other caller tapes and the already-emitted output are preserved exactly. -/
theorem arithmetic_hoare (L V v d M : Nat) (s : Bool) (inp : Tape)
    (work : Fin 17 → Tape) (ys : List Bool) (hi : Parked inp) (hp : ∀ i, Parked (work i))
    (hL : work 15 = regTape L) (hV : work 16 = regTape V) (hv : work 5 = regTape v)
    (hd : work 11 = regTape d) (hLm : L ≤ M) (hVm : V ≤ M) (hvm : v ≤ M)
    (hdm : d ≤ M) (hbase : FormulaRailBase.value L V v s ≤ M) :
    (machine s).HoareTime (EmitPred inp work ys)
      (EmitPred inp (bank work (FormulaRailBase.value L V v s)) ys)
      (40*(opBudget M+1)) := by
  have he : 1+bit s+V+(20+bit s)*L+2*v+2*(L*v) = FormulaRailBase.value L V v s := by
    cases s <;> simp [bit,FormulaRailBase.value] <;> ring
  have hx : 1+bit s+V+(20+bit s)*L+2*v+2*(L*v) ≤ M := he ▸ hbase
  have hinit := (setConstTM_hoareTime (11 : Fin 17) (1+bit s) d inp work ys hi hp hd).mono_bound
    (setConstTM_le_opBudget (by omega) hdm)
  have hA := add_step 16 (by decide) V M (1+bit s) inp work ys hi hp hV hVm (by omega)
  have hB := repeat_hoare (addIntoTM (15 : Fin 17) 11) L M (opBudget M) inp work ys hi hp
    (fun z hz => add_step 15 (by decide) L M z inp work ys hi hp hL hLm hz)
    (20+bit s) (1+bit s+V) (by omega)
  have hC := repeat_hoare (addIntoTM (5 : Fin 17) 11) v M (opBudget M) inp work ys hi hp
    (fun z hz => add_step 5 (by decide) v M z inp work ys hi hp hv hvm hz)
    2 (1+bit s+V+(20+bit s)*L) (by omega)
  have hD := repeat_hoare (mulAddIntoTM (15 : Fin 17) 5 11) (L*v) M (opBudget M) inp work ys hi hp
    (fun z hz => product_step L v M z inp work ys hi hp hL hv hLm hvm hz)
    2 (1+bit s+V+(20+bit s)*L+2*v) hx
  have hCD := seqTM_hoareTime _ _ hC (emitPred_transition hi (parked work hp _) ys) hD
  have hBCD := seqTM_hoareTime _ _ hB (emitPred_transition hi (parked work hp _) ys) hCD
  have hABCD := seqTM_hoareTime _ _ hA (emitPred_transition hi (parked work hp _) ys) hBCD
  have h := seqTM_hoareTime _ _ hinit (emitPred_transition hi (parked work hp _) ys) hABCD
  rw [he] at h
  exact h.mono_bound (by cases s <;> simp [bit] <;> omega)

end UnconstrainedPACDetection.FormulaRailBaseRegisters

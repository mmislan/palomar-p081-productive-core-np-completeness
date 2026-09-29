module

public import proofs.IrrRAFEnumeration.CompletionBaseInit
public import proofs.Complexitylib.Models.TuringMachine.Registers.Horner

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

/-- The four operations used by the fixed base-compiler setup and reloads. -/
inductive BaseRegOp where
  | set (dst : Fin 23) (value : Nat)
  | copy (src dst : Fin 23)
  | add (src dst : Fin 23)
  | mul (src other dst : Fin 23)

def BaseRegOp.machine : BaseRegOp → TM 23
  | .set q c => setConstTM q c
  | .copy p q => copyIntoTM p q
  | .add p q => addIntoTM p q
  | .mul p s q => mulAddIntoTM p s q

def BaseRegOp.valid : BaseRegOp → Prop
  | .set _ _ => True
  | .copy p q => p ≠ q
  | .add p q => p ≠ q
  | .mul p s q => p ≠ s ∧ p ≠ q ∧ s ≠ q

def BaseRegOp.eval : BaseRegOp → (Fin 23 → Nat) → (Fin 23 → Nat)
  | .set q c,v => Function.update v q c
  | .copy p q,v => Function.update v q (v p)
  | .add p q,v => Function.update v q (v q+v p)
  | .mul p s q,v => Function.update v q (v q+v p*v s)

def baseRegWork (v : Fin 23 → Nat) : Fin 23 → Tape := fun i => regTape (v i)

theorem baseRegWork_update (v : Fin 23 → Nat) (q : Fin 23) (a : Nat) :
    baseRegWork (Function.update v q a) = Function.update (baseRegWork v) q (regTape a) := by
  funext i
  by_cases h : i = q
  · subst i; simp [baseRegWork]
  · simp [baseRegWork,Function.update_of_ne h]

theorem BaseRegOp.correct (op : BaseRegOp) (v : Fin 23 → Nat) (M : Nat)
    (hv : ∀ i, v i ≤ M) (ho : ∀ i, op.eval v i ≤ M) (hok : op.valid)
    (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    op.machine.HoareTime (EmitPred inp (baseRegWork v) ys)
      (EmitPred inp (baseRegWork (op.eval v)) ys) (opBudget M) := by
  cases op with
  | set q c =>
    have h := setConstTM_hoareTime q c (v q) inp (baseRegWork v) ys hp
      (fun _ => parked_regTape _) rfl
    have hc : c ≤ M := by simpa [BaseRegOp.eval] using ho q
    simpa only [BaseRegOp.machine,BaseRegOp.eval,baseRegWork_update] using
      h.mono_bound (setConstTM_le_opBudget hc (hv q))
  | copy p q =>
    have h := copyIntoTM_hoareTime p q hok (v p) (v q) inp (baseRegWork v) ys hp
      (fun _ _ => parked_regTape _) rfl rfl
    simpa only [BaseRegOp.machine,BaseRegOp.eval,baseRegWork_update] using
      h.mono_bound (copyIntoTM_le_opBudget (hv p) (hv q))
  | add p q =>
    have h := addIntoTM_hoareTime p q hok (v p) (v q) inp (baseRegWork v) ys hp
      (fun _ _ => parked_regTape _) rfl rfl
    have hc : v q+v p ≤ M := by simpa [BaseRegOp.eval] using ho q
    simpa only [BaseRegOp.machine,BaseRegOp.eval,baseRegWork_update] using
      h.mono_bound (addIntoTM_le_opBudget (hv p) hc)
  | mul p s q =>
    have h := mulAddIntoTM_hoareTime p s q hok.1 hok.2.1 hok.2.2
      (v p) (v s) (v q) inp (baseRegWork v) ys hp
      (fun _ _ => parked_regTape _) rfl rfl rfl
    have hc : v q+v p*v s ≤ M := by simpa [BaseRegOp.eval] using ho q
    simpa only [BaseRegOp.machine,BaseRegOp.eval,baseRegWork_update] using
      h.mono_bound (mulAddIntoTM_le_opBudget (hv p) (hv s) hc)

/-- Registers 0..11 are emitter scratch; 12..22 hold shared dimensions/addresses. -/
def baseBankOps : List BaseRegOp :=
  [.copy 12 14,.mul 12 14 15,.copy 15 17,.add 13 17,
   .copy 17 16,.add 12 16,.set 18 3,.add 12 18,.add 13 18,
   .copy 18 19,.add 12 19,.copy 19 20,.add 12 20,
   .copy 20 21,.add 12 21,.copy 12 22,.add 12 22,.add 12 22,.add 13 14]

def baseBankInitial (d r : Nat) : Fin 23 → Nat :=
  Function.update (Function.update (fun _ => 0) 12 d) 13 r

def baseBankStage (d r k : Nat) : Fin 23 → Nat :=
  ((baseBankOps.take k).foldl (fun v op => op.eval v) (baseBankInitial d r))

def baseBankCap (d r : Nat) := d*d+5*d+r+3

def baseBankTM : TM 23 := bigSeqTM (baseBankOps.map BaseRegOp.machine)

set_option maxHeartbeats 2000000 in
theorem baseBankStage_bound (d r k : Nat) (hk : k ≤ 19) (q : Fin 23) :
    baseBankStage d r k q ≤ baseBankCap d r := by
  interval_cases k <;> fin_cases q <;>
    simp [baseBankStage,baseBankOps,BaseRegOp.eval,baseBankInitial,baseBankCap] <;> omega

theorem baseBankStage_step (d r k : Nat) (hk : k < baseBankOps.length) :
    baseBankStage d r (k+1) = (baseBankOps[k]).eval (baseBankStage d r k) := by
  unfold baseBankStage
  rw [List.take_succ_eq_append_getElem hk,List.foldl_append]
  rfl

theorem baseBankTM_correct (d r : Nat) (inp : Tape) (ys : List Bool) (hp : Parked inp) :
    baseBankTM.HoareTime (EmitPred inp (baseRegWork (baseBankInitial d r)) ys)
      (EmitPred inp (baseRegWork (baseBankStage d r 19)) ys)
      (19*(opBudget (baseBankCap d r)+1)+1) := by
  have h := bigSeqTM_hoareTime (baseBankOps.map BaseRegOp.machine) inp
    (fun k => baseRegWork (baseBankStage d r k)) (fun _ => ys)
    (opBudget (baseBankCap d r)) hp (fun _ _ => parked_regTape _) (by
      intro k hk
      have hk' : k < baseBankOps.length := by simpa using hk
      have hk19 : k < 19 := hk'
      simp only [List.getElem_map]
      rw [baseBankStage_step d r k hk']
      apply BaseRegOp.correct
      · exact fun i => baseBankStage_bound d r k (by omega) i
      · intro i
        rw [← baseBankStage_step d r k hk']
        exact baseBankStage_bound d r (k+1) (by omega) i
      · interval_cases k <;> simp [baseBankOps,BaseRegOp.valid]
      · exact hp)
  exact h

end IrrRAFEnumeration.CompletionQuery

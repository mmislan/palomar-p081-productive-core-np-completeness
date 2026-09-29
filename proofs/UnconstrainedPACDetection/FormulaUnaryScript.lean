module

public import proofs.UnconstrainedPACDetection.FormulaHeaderFrame

@[expose] public section

namespace UnconstrainedPACDetection.FormulaUnaryScript
open Complexity Complexity.TM

inductive Op (n : Nat) where
  | set (dst : Fin n) (c : Nat)
  | inc (dst : Fin n)
  | copy (src dst : Fin n) (hne : src ≠ dst)
  | mulAdd (a b dst : Fin n) (hab : a≠b) (had : a≠dst) (hbd : b≠dst)

def eval {n : Nat} (op : Op n) (v : Fin n → Nat) : Fin n → Nat := match op with
  | .set d c => Function.update v d c
  | .inc d => Function.update v d (v d+1)
  | .copy s d _ => Function.update v d (v s)
  | .mulAdd a b d _ _ _ => Function.update v d (v d+v a*v b)

def compile {n : Nat} : Op n → TM n
  | .set d c => setConstTM d c
  | .inc d => incRegTM d
  | .copy s d _ => copyIntoTM s d
  | .mulAdd a b d _ _ _ => mulAddIntoTM a b d

def frame {n : Nat} (v : Fin n → Nat) : Fin n → Tape := fun t => regTape (v t)

theorem update_frame {n : Nat} (v : Fin n → Nat) (d : Fin n) (x : Nat) :
    Function.update (frame v) d (regTape x) = frame (Function.update v d x) := by
  funext t
  by_cases h : t=d
  · subst t; simp [frame]
  · simp only [Function.update_of_ne h,frame]

def Allowed {n : Nat} (op : Op n) (v : Fin n → Nat) (M : Nat) : Prop := match op with
  | .set d c => c≤M ∧ v d≤M
  | .inc d => v d≤M
  | .copy s d _ => v s≤M ∧ v d≤M
  | .mulAdd a b d _ _ _ => v a≤M ∧ v b≤M ∧ v d+v a*v b≤M

theorem op_hoare {n : Nat} (op : Op n) (v : Fin n → Nat) (M : Nat)
    (ha : Allowed op v M)
    (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    (compile op).HoareTime (EmitPred inp (frame v) ys) (EmitPred inp (frame (eval op v)) ys) (opBudget M) := by
  cases op with
  | set d c =>
    have h := setConstTM_hoareTime d c (v d) inp (frame v) ys hi (fun t => parked_regTape _) rfl
    rw [update_frame] at h
    exact h.mono_bound (setConstTM_le_opBudget ha.1 ha.2)
  | inc d =>
    have h := incRegTM_hoareTime d (v d) inp (frame v) ys hi (fun t _ => parked_regTape _) rfl
    rw [update_frame] at h
    exact h.mono_bound (incRegTM_le_opBudget ha)
  | copy s d hne =>
    have h := copyIntoTM_hoareTime s d hne (v s) (v d) inp (frame v) ys hi (fun t _ => parked_regTape _) rfl rfl
    rw [update_frame] at h
    exact h.mono_bound (copyIntoTM_le_opBudget ha.1 ha.2)
  | mulAdd a b d hab had hbd =>
    have h := mulAddIntoTM_hoareTime a b d hab had hbd (v a) (v b) (v d) inp (frame v) ys hi
      (fun t _ => parked_regTape _) rfl rfl rfl
    rw [update_frame] at h
    exact h.mono_bound (mulAddIntoTM_le_opBudget ha.1 ha.2.1 ha.2.2)

def run {n : Nat} (ops : List (Op n)) (v : Fin n → Nat) : Fin n → Nat := ops.foldl (fun w op => eval op w) v

def machine {n : Nat} (ops : List (Op n)) : TM n := ops.foldr (fun op m => seqTM (compile op) m) (emitBitsTM [])

def Safe {n : Nat} : List (Op n) → (Fin n → Nat) → Nat → Prop
  | [],_,_ => True
  | op::ops,v,M => Allowed op v M ∧ Safe ops (eval op v) M

theorem hoare {n : Nat} (ops : List (Op n)) (v : Fin n → Nat) (M : Nat) (hs : Safe ops v M)
    (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    (machine ops).HoareTime (EmitPred inp (frame v) ys) (EmitPred inp (frame (run ops v)) ys)
      (ops.length*(opBudget M+1)) := by
  induction ops generalizing v with
  | nil =>
    unfold EmitPred
    simpa only [machine,List.foldr_nil,run,List.foldl_nil,List.length_nil,Nat.zero_mul,List.append_nil]
      using emitBitsTM_hoareTime [] inp (frame v) ys hi (fun t => parked_regTape _)
  | cons op ops ih =>
    have h0 := op_hoare op v M hs.1 inp hi ys
    have h1 := ih (eval op v) hs.2
    have h := seqTM_hoareTime _ _ h0 (emitPred_transition hi (fun t => parked_regTape _) _) h1
    exact h.mono_bound (by simp only [List.length_cons,Nat.add_mul]; omega)

end UnconstrainedPACDetection.FormulaUnaryScript

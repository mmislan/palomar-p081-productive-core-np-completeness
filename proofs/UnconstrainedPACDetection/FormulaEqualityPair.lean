module

public import proofs.UnconstrainedPACDetection.FormulaPairExecution
public import proofs.Complexitylib.Models.TuringMachine.Registers.DecReg

@[expose] public section

namespace UnconstrainedPACDetection.FormulaEqualityPair
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)
open FormulaCoefficientPlan (Plan)
open FormulaPairExecution (place_hoare)

def small (x y : Nat) : Fin 4 → Tape := FormulaClauseCompare.bank x y [true]

theorem inc_hoare (x y : Nat) (ys : List Bool) (inp : Tape) (hi : Parked inp) :
    (incRegTM (0 : Fin 4)).HoareTime (EmitPred inp (small x y) ys)
      (EmitPred inp (small (x+1) y) ys) (2*x+4) := by
  have h := incRegTM_hoareTime (0 : Fin 4) x inp (small x y) ys hi
    (fun t _ => FormulaClauseCompare.bank_parked x y [true] t) rfl
  have he : Function.update (small x y) 0 (regTape (x+1)) = small (x+1) y := by
    funext t; fin_cases t <;> simp [small,FormulaClauseCompare.bank]
  rw [he] at h
  exact h

theorem dec_hoare (x y : Nat) (ys : List Bool) (inp : Tape) (hi : Parked inp) :
    (decRegTM (0 : Fin 4)).HoareTime (EmitPred inp (small (x+1) y) ys)
      (EmitPred inp (small x y) ys) (2*x+6) := by
  have h := decRegTM_hoareTime (0 : Fin 4) (x+1) inp (small (x+1) y) ys hi
    (fun t _ => FormulaClauseCompare.bank_parked (x+1) y [true] t) rfl
  have he : Function.update (small (x+1) y) 0 (regTape (x+1-1)) = small x y := by
    funext t; fin_cases t <;> simp [small,FormulaClauseCompare.bank]
  rw [he] at h
  exact h.mono_bound (by omega)

def query (offset : Bool) : TM 4 := if offset then
  seqTM (incRegTM 0) (seqTM FormulaClauseCompare.machine (decRegTM 0))
  else FormulaClauseCompare.machine

theorem query_hoare (offset : Bool) (x y : Nat) (ys : List Bool) (inp : Tape)
    (hi : Parked inp) : (query offset).HoareTime (EmitPred inp (small x y) ys)
      (EmitPred inp (small x y) (ys ++ [decide (x+(if offset then 1 else 0)=y)]))
      (4*x+3*max (x+1) y+32) := by
  cases offset with
  | false =>
    have h := FormulaClauseCompare.compare_hoare x y [true] ys inp hi
    simp only [List.isEmpty_cons,Bool.not_false,Bool.and_true] at h
    simpa only [query, small, Bool.false_eq_true,ite_false,Nat.add_zero] using
      h.mono_bound (show 3*max x y+20 ≤ 4*x+3*max (x+1) y+32 by omega)
  | true =>
    have hc := FormulaClauseCompare.compare_hoare (x+1) y [true] ys inp hi
    simp only [List.isEmpty_cons,Bool.not_false,Bool.and_true] at hc
    have hd := dec_hoare x y (ys ++ [decide (x+1=y)]) inp hi
    have h2 := seqTM_hoareTime _ _ hc
      (emitPred_transition hi (FormulaClauseCompare.bank_parked (x+1) y [true]) _) hd
    have h := seqTM_hoareTime _ _ (inc_hoare x y ys inp hi)
      (emitPred_transition hi (FormulaClauseCompare.bank_parked (x+1) y [true]) _) h2
    exact h.mono_bound (by omega)

def bank (x y z w r a b : Nat) : Fin 13 → Tape :=
  ![regTape x,regTape y,word [],word [true],regTape z,regTape w,word [],word [true],
    regTape r,regTape a,regTape b,word [],word [true]]

theorem parked (x y z w r a b : Nat) : ∀ t, Parked (bank x y z w r a b t) := by
  intro t; fin_cases t
  all_goals first | exact parked_regTape _ | exact word_parked _

def body (off₁ off₂ right : Bool) (p : Plan) : TM 13 :=
  seqTM (placeWorkTM 0 9 (query off₁)) (FormulaCoefficientGate.gate
    (seqTM (placeWorkTM 4 5 (query off₂)) (FormulaCoefficientGate.gate
      (placeWorkTM 8 0 (FormulaCoefficientRound.machine right p)))))

theorem body_hoare (off₁ off₂ right : Bool) (p : Plan) (x y z w r a b : Nat)
    (ys : List Bool) (inp : Tape) (hi : Parked inp) :
    (body off₁ off₂ right p).HoareTime (EmitPred inp (bank x y z w r a b) ys)
      (EmitPred inp (bank x y z w r a b)
        (ys ++ if x+(if off₁ then 1 else 0)=y ∧ z+(if off₂ then 1 else 0)=w then
          BinaryFields.encodeField (FormulaCoefficientPlan.value p r (if right then b else a)).bits else []))
      (4*x+4*z+3*max (x+1) y+3*max (z+1) w+3*max r (if right then b else a)+97) := by
  have hp := parked x y z w r a b
  have hc := place_hoare _ 8 0 _ _ (bank x y z w r a b) _ _ _ hp
    (by intro t; fin_cases t <;> rfl)
    (FormulaCoefficientRound.operation_hoare right p r a b ys inp hi)
  have hg := FormulaCoefficientGate.gate_hoare _ (decide (z+(if off₂ then 1 else 0)=w))
    _ _ ys _ _ hi hp hc
  have hq₂ := place_hoare _ 4 5 _ _ (bank x y z w r a b) _ _ _ hp
    (by intro t; fin_cases t <;> rfl) (query_hoare off₂ z w ys inp hi)
  have h₂ := seqTM_hoareTime _ _ hq₂ (emitPred_transition hi hp _) hg
  have hg₁ := FormulaCoefficientGate.gate_hoare _ (decide (x+(if off₁ then 1 else 0)=y))
    _ _ ys _ _ hi hp h₂
  have hq₁ := place_hoare _ 0 9 _ _ (bank x y z w r a b) _ _ _ hp
    (by intro t; fin_cases t <;> rfl) (query_hoare off₁ x y ys inp hi)
  have h := seqTM_hoareTime _ _ hq₁ (emitPred_transition hi hp _) hg₁
  have h' := h.mono_bound (show (4*x+3*max (x+1) y+32)+1+
      ((4*z+3*max (z+1) w+32)+1+(3*max r (if right then b else a)+27+2)+2) ≤
      4*x+4*z+3*max (x+1) y+3*max (z+1) w+3*max r (if right then b else a)+97 by omega)
  by_cases h₁ : x+(if off₁ then 1 else 0)=y <;>
    by_cases h₂ : z+(if off₂ then 1 else 0)=w <;> simpa [body,h₁,h₂] using h'

end UnconstrainedPACDetection.FormulaEqualityPair

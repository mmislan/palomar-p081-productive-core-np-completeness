module

public import proofs.UnconstrainedPACDetection.FormulaSwitchHeadRound

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchHeadPorts
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaSwitchVariableHeads (bank parked)

def round (p q : ControlSwitch.V) (skipSink right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 20 :=
  if skipSink && decide (q=4) then emitBitsTM [] else FormulaSwitchHeadRound.machine p q right plan

def machine (p : ControlSwitch.V) (skipSink right : Bool) (plan : FormulaCoefficientPlan.Plan) :
    List ControlSwitch.V → TM 20
  | [] => emitBitsTM []
  | q::qs => seqTM (seqTM (round p q skipSink right plan) (incRegTM 11)) (machine p skipSink right plan qs)

def fields (φ : SAT.CNF) (i j : Fin (levels φ)) (p : ControlSwitch.V)
    (skipSink right : Bool) (plan : FormulaCoefficientPlan.Plan) (r a : Nat) :
    List ControlSwitch.V → Nat → List Bool
  | [],_ => []
  | q::qs,b => (if skipSink && decide (q=4) then [] else FormulaSwitchHeadRound.field φ i j p q right plan r a b) ++
      fields φ i j p skipSink right plan r a qs (b+1)

/-- Finite port order is implemented by one fixed sequence; every index increments physically. -/
theorem hoare (φ : SAT.CNF) (i j : Fin (levels φ)) (p : ControlSwitch.V)
    (skipSink right : Bool) (plan : FormulaCoefficientPlan.Plan) (v r a f g M : Nat)
    (hr : r ≤ M) (ha : a ≤ M) (qs : List ControlSwitch.V) (b : Nat) (hb : b+qs.length ≤ M)
    (ys : List Bool) : (machine p skipSink right plan qs).HoareTime
      (EmitPred (word φ.encode) (bank i.val v j.val r a b f (levels φ) (varCount φ) g φ.length) ys)
      (EmitPred (word φ.encode) (bank i.val v j.val r a (b+qs.length) f (levels φ) (varCount φ) g φ.length)
        (ys ++ fields φ i j p skipSink right plan r a qs b))
      (qs.length*(7*levels φ+5*M+109)) := by
  induction qs generalizing b ys with
  | nil =>
    unfold EmitPred
    simpa only [machine,fields,List.length_nil,Nat.add_zero,Nat.zero_mul,List.append_nil] using
      emitBitsTM_hoareTime ([] : List Bool) (word φ.encode)
        (bank i.val v j.val r a b f (levels φ) (varCount φ) g φ.length) ys
        (word_parked _) (parked _ _ _ _ _ _ _ _ _ _ _)
  | cons q qs ih =>
    let zs := if skipSink && decide (q=4) then [] else FormulaSwitchHeadRound.field φ i j p q right plan r a b
    have hq : (round p q skipSink right plan).HoareTime
        (EmitPred (word φ.encode) (bank i.val v j.val r a b f (levels φ) (varCount φ) g φ.length) ys)
        (EmitPred (word φ.encode) (bank i.val v j.val r a b f (levels φ) (varCount φ) g φ.length) (ys ++ zs))
        (7*levels φ+3*M+103) := by
      by_cases hs : (skipSink && decide (q=4)) = true
      · unfold EmitPred
        simpa only [round,zs,ite_eq_left hs,List.append_nil] using
          (emitBitsTM_hoareTime ([] : List Bool) (word φ.encode)
            (bank i.val v j.val r a b f (levels φ) (varCount φ) g φ.length) ys
            (word_parked _) (parked _ _ _ _ _ _ _ _ _ _ _)).mono_bound
              (show 0 ≤ 7*levels φ+3*M+103 by omega)
      · have h := FormulaSwitchHeadRound.hoare φ i j p q right plan v r a b f g ys
        have h' := h.mono_bound (show 7*levels φ+3*max r (if right then b else a)+103 ≤
            7*levels φ+3*M+103 by cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> simp only [List.length_cons] at hb <;> omega)
        simpa only [round,zs,ite_eq_right hs] using h'
    have hc := incRegTM_hoareTime (11 : Fin 20) b (word φ.encode)
      (bank i.val v j.val r a b f (levels φ) (varCount φ) g φ.length) (ys ++ zs)
      (word_parked _) (fun t _ => parked _ _ _ _ _ _ _ _ _ _ _ t) rfl
    have he : Function.update (bank i.val v j.val r a b f (levels φ) (varCount φ) g φ.length) 11 (regTape (b+1)) =
        bank i.val v j.val r a (b+1) f (levels φ) (varCount φ) g φ.length := by
      funext t; fin_cases t <;> simp [bank,FormulaSwitchVariableHeads.extend,
        FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
    rw [he] at hc
    have hstep := seqTM_hoareTime _ _ hq (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _ _ _) _) hc
    have hrest := ih (b+1) (by simp only [List.length_cons] at hb; omega) (ys ++ zs)
    have h := seqTM_hoareTime _ _ hstep (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _ _ _) _) hrest
    have h' := h.mono_bound (show (7*levels φ+3*M+103)+1+(2*b+4)+1+
        qs.length*(7*levels φ+5*M+109) ≤ (q::qs).length*(7*levels φ+5*M+109) by
      simp only [List.length_cons] at hb ⊢
      nlinarith)
    have hindex : b+(q::qs).length = b+1+qs.length := by simp only [List.length_cons]; omega
    have hy : ys ++ fields φ i j p skipSink right plan r a (q::qs) b =
        (ys ++ zs) ++ fields φ i j p skipSink right plan r a qs (b+1) := by
      simp only [fields,zs,List.append_assoc]
    rw [hindex,hy]
    exact h'

end UnconstrainedPACDetection.FormulaSwitchHeadPorts

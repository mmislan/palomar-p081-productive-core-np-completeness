module

public import proofs.UnconstrainedPACDetection.FormulaSwitchVariableHeads
public import proofs.UnconstrainedPACDetection.FormulaSwitchPair

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchHeadRound
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaSwitchVariableHeads (bank parked)
open FormulaSwitchPair (mode first second enabled offset)

def forwardRoute : Equiv.Perm (Fin 20) where
  toFun := ![0,6,2,8,3,1,7,13,9,10,11,12,19,4,5,14,15,16,17,18]
  invFun := ![0,5,2,4,13,14,1,6,3,8,9,10,11,7,15,16,17,18,19,12]
  left_inv := by intro t; fin_cases t <;> rfl
  right_inv := by intro t; fin_cases t <;> rfl

def route (back : Bool) : Equiv.Perm (Fin 20) :=
  if back then forwardRoute.trans (Equiv.swap 0 6) else forwardRoute

def machine (p q : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 20 :=
  VerifierWorkPermutation.machine (placeWorkTM 0 7
    (FormulaVariablePair.machine (enabled (mode p q)) (offset (mode p q)) false right plan))
      (route (decide (mode p q = .backward)))

theorem guard_hoare (on off right : Bool) (plan : FormulaCoefficientPlan.Plan)
    (x y r a b : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    (FormulaVariablePair.machine on off false right plan).HoareTime
      (EmitPred inp (FormulaEqualityPair.bank x y 0 0 r a b) ys)
      (EmitPred inp (FormulaEqualityPair.bank x y 0 0 r a b)
        (ys ++ if on=true ∧ x+(if off then 1 else 0)=y ∧ 0+(if false then 1 else 0)=0 then
          BinaryFields.encodeField (FormulaCoefficientPlan.value plan r (if right then b else a)).bits else []))
      (4*x+3*max (x+1) y+3*max r (if right then b else a)+100) := by
  cases on
  · have h := emitBitsTM_hoareTime ([] : List Bool) inp (FormulaEqualityPair.bank x y 0 0 r a b) ys hi
      (FormulaEqualityPair.parked _ _ _ _ _ _ _)
    unfold EmitPred
    simpa only [FormulaVariablePair.machine,Bool.false_eq_true,ite_false,false_and,List.append_nil] using
      h.mono_bound (show 0 ≤ 4*x+3*max (x+1) y+3*max r (if right then b else a)+100 by omega)
  · have h := FormulaEqualityPair.body_hoare off false right plan x y 0 0 r a b ys inp hi
    have h' := h.mono_bound (show 4*x+4*0+3*max (x+1) y+3*max (0+1) 0+
        3*max r (if right then b else a)+97 ≤
        4*x+3*max (x+1) y+3*max r (if right then b else a)+100 by omega)
    simpa only [FormulaVariablePair.machine,ite_true,true_and,Bool.true_eq] using h'

def field (φ : SAT.CNF) (i j : Fin (levels φ)) (p q : ControlSwitch.V)
    (right : Bool) (plan : FormulaCoefficientPlan.Plan) (r a b : Nat) : List Bool :=
  if FormulaWiring.adjacency φ (SwitchStack.sw i p) (SwitchStack.sw j q)
  then BinaryFields.encodeField (FormulaCoefficientPlan.value plan r (if right then b else a)).bits else []

/-- Execute a switch comparison from the common caller frame, including backward routing. -/
theorem hoare (φ : SAT.CNF) (i j : Fin (levels φ)) (p q : ControlSwitch.V)
    (right : Bool) (plan : FormulaCoefficientPlan.Plan) (v r a b f g : Nat) (ys : List Bool) :
    (machine p q right plan).HoareTime
      (EmitPred (word φ.encode) (bank i.val v j.val r a b f (levels φ) (varCount φ) g φ.length) ys)
      (EmitPred (word φ.encode) (bank i.val v j.val r a b f (levels φ) (varCount φ) g φ.length)
        (ys ++ field φ i j p q right plan r a b))
      (7*levels φ+3*max r (if right then b else a)+103) := by
  have h := guard_hoare (enabled (mode p q)) (offset (mode p q)) right plan
    (first (mode p q) i.val j.val) (second (mode p q) i.val j.val) r a b (word φ.encode) (word_parked _) ys
  have hr := FormulaRoutedFrame.hoare _ 0 7 (route (decide (mode p q = .backward))) _ _
    (bank i.val v j.val r a b f (levels φ) (varCount φ) g φ.length) _ _ _
    (parked _ _ _ _ _ _ _ _ _ _ _) (by
      intro t
      by_cases hm : mode p q = .backward
      · simp only [first,second,hm,decide_true,route,ite_true]
        fin_cases t <;> first | rfl | exact FormulaEndpointRegisters.unary_word 0
      · simp only [first,second,hm,decide_false,route,Bool.false_eq_true,ite_false]
        fin_cases t <;> first | rfl | exact FormulaEndpointRegisters.unary_word 0) h
  simp only [← FormulaSwitchPair.admission] at hr
  apply hr.mono_bound
  have hi := i.isLt
  have hj := j.isLt
  unfold first second
  split_ifs <;> omega

end UnconstrainedPACDetection.FormulaSwitchHeadRound

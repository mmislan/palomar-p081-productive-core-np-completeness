module

public import proofs.UnconstrainedPACDetection.FormulaSwitchHeadLevels

@[expose] public section

namespace UnconstrainedPACDetection.FormulaAllSwitchHeads
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaSwitchVariableHeads (bank parked)
open FormulaChangingFrame (extend)

def prepare : TM 21 := seqTM (clearRegTM 6) (seqTM (copyIntoTM 15 20) (decRegTM 20))

theorem prepare_hoare (i v j r a f L V g C h : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    prepare.HoareTime
      (EmitPred inp (extend (bank i v j r a 0 f L V g C) (regTape h)) ys)
      (EmitPred inp (extend (bank i v 0 r a 0 f L V g C) (regTape (L-1))) ys)
      (2*L^2+9*L+2*h+2*j+17) := by
  have hp (k t : Nat) := FormulaChangingFrame.parked (bank i v k r a 0 f L V g C) (regTape t)
    (parked _ _ _ _ _ _ _ _ _ _ _) (parked_regTape _)
  have h0 := clearRegTM_hoareTime (6 : Fin 21) j inp
    (extend (bank i v j r a 0 f L V g C) (regTape h)) ys hi (fun t _ => hp j h t) rfl
  have he0 : Function.update (extend (bank i v j r a 0 f L V g C) (regTape h)) 6 (regTape 0) =
      extend (bank i v 0 r a 0 f L V g C) (regTape h) := by
    funext t; fin_cases t <;> simp [extend,bank,FormulaSwitchVariableHeads.extend,
      FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he0] at h0
  have h1 := copyIntoTM_hoareTime (15 : Fin 21) 20 (by decide) L h inp
    (extend (bank i v 0 r a 0 f L V g C) (regTape h)) ys hi (fun t _ => hp 0 h t) rfl rfl
  have he1 : Function.update (extend (bank i v 0 r a 0 f L V g C) (regTape h)) 20 (regTape L) =
      extend (bank i v 0 r a 0 f L V g C) (regTape L) := by
    funext t; fin_cases t <;> simp [extend]
  rw [he1] at h1
  have h2 := decRegTM_hoareTime (20 : Fin 21) L inp
    (extend (bank i v 0 r a 0 f L V g C) (regTape L)) ys hi (fun t _ => hp 0 L t) rfl
  have he2 : Function.update (extend (bank i v 0 r a 0 f L V g C) (regTape L)) 20 (regTape (L-1)) =
      extend (bank i v 0 r a 0 f L V g C) (regTape (L-1)) := by
    funext t; fin_cases t <;> simp [extend]
  rw [he2] at h2
  have h12 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (hp 0 L) _) h2
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (hp 0 h) _) h12).mono_bound (by nlinarith)

def ready (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 :=
  seqTM (placeWorkTM 0 1 (FormulaSwitchHeadLevels.body p true right plan))
    (FormulaSwitchHeadLevels.loop p right plan)

def bits (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V)
    (right : Bool) (plan : FormulaCoefficientPlan.Plan) (r a : Nat) : List Bool :=
  FormulaSwitchHeadLevels.fields φ i ⟨0,FormulaWiring.levels_pos φ⟩ p true right plan r a ++
    FormulaSwitchHeadLevels.laterBits φ i p right plan r a (levels φ-1)

def readyBudget (φ : SAT.CNF) := FormulaSwitchHeadLevels.bodyBudget φ+1+
  ((levels φ-1)*(FormulaSwitchHeadLevels.bodyBudget φ+2)+(levels φ+1))

theorem ready_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V)
    (right : Bool) (plan : FormulaCoefficientPlan.Plan) (v r a f g : Nat)
    (hr : r ≤ (FormulaIndexedGraph.labels φ).length) (ha : a ≤ (FormulaIndexedGraph.labels φ).length)
    (ys : List Bool) : (ready p right plan).HoareTime
      (EmitPred (word φ.encode) (extend (bank i.val v 0 r a 0 f (levels φ) (varCount φ) g φ.length)
        (regTape (levels φ-1))) ys)
      (EmitPred (word φ.encode) (extend (bank i.val v (levels φ) r a (20*levels φ) f (levels φ) (varCount φ) g φ.length)
        (regTape (levels φ-1))) (ys ++ bits φ i p right plan r a)) (readyBudget φ) := by
  have h0 := FormulaSwitchHeadLevels.body_hoare φ i ⟨0,FormulaWiring.levels_pos φ⟩ p true right plan v r a f g hr ha ys
  have h0' := FormulaChangingFrame.append_hoare _ _ _ _ (regTape (levels φ-1)) _ _ _
    (parked _ _ _ _ _ _ _ _ _ _ _) (parked_regTape _) h0
  have h1 := FormulaSwitchHeadLevels.loop_hoare φ i p right plan v r a f g hr ha
    (ys ++ FormulaSwitchHeadLevels.fields φ i ⟨0,FormulaWiring.levels_pos φ⟩ p true right plan r a)
  have h := seqTM_hoareTime _ _ h0' (emitPred_transition (word_parked _)
    (FormulaChangingFrame.parked _ _ (parked _ _ _ _ _ _ _ _ _ _ _) (parked_regTape _)) _) h1
  simpa only [ready,readyBudget,bits,List.append_assoc] using h

def machine (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 :=
  seqTM prepare (ready p right plan)

theorem hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V)
    (right : Bool) (plan : FormulaCoefficientPlan.Plan) (v j r a f g h : Nat)
    (hr : r ≤ (FormulaIndexedGraph.labels φ).length) (ha : a ≤ (FormulaIndexedGraph.labels φ).length)
    (ys : List Bool) : (machine p right plan).HoareTime
      (EmitPred (word φ.encode) (extend (bank i.val v j r a 0 f (levels φ) (varCount φ) g φ.length)
        (regTape h)) ys)
      (EmitPred (word φ.encode) (extend (bank i.val v (levels φ) r a (20*levels φ) f (levels φ) (varCount φ) g φ.length)
        (regTape (levels φ-1))) (ys ++ bits φ i p right plan r a))
      (2*(levels φ)^2+9*levels φ+2*h+2*j+18+readyBudget φ) := by
  have h0 := prepare_hoare i.val v j r a f (levels φ) (varCount φ) g φ.length h (word φ.encode) (word_parked _) ys
  have h1 := ready_hoare φ i p right plan v r a f g hr ha ys
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _)
    (FormulaChangingFrame.parked _ _ (parked _ _ _ _ _ _ _ _ _ _ _) (parked_regTape _)) _) h1).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaAllSwitchHeads

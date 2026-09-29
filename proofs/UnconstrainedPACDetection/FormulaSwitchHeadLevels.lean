module

public import proofs.UnconstrainedPACDetection.FormulaSwitchHeadPorts
public import proofs.UnconstrainedPACDetection.FormulaChangingFrame

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchHeadLevels
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaSwitchVariableHeads (bank parked)
open FormulaChangingFrame (extend)

def cap (φ : SAT.CNF) := (FormulaIndexedGraph.labels φ).length+20*levels φ
def bodyBudget (φ : SAT.CNF) := 20*(7*levels φ+5*cap φ+109)+2*levels φ+5

def body (p : ControlSwitch.V) (skipSink right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 20 :=
  seqTM (FormulaSwitchHeadPorts.machine p skipSink right plan (List.finRange 20)) (incRegTM 6)

def fields (φ : SAT.CNF) (i j : Fin (levels φ)) (p : ControlSwitch.V)
    (skipSink right : Bool) (plan : FormulaCoefficientPlan.Plan) (r a : Nat) : List Bool :=
  FormulaSwitchHeadPorts.fields φ i j p skipSink right plan r a (List.finRange 20) (20*j.val)

theorem body_hoare (φ : SAT.CNF) (i j : Fin (levels φ)) (p : ControlSwitch.V)
    (skipSink right : Bool) (plan : FormulaCoefficientPlan.Plan) (v r a f g : Nat)
    (hr : r ≤ (FormulaIndexedGraph.labels φ).length) (ha : a ≤ (FormulaIndexedGraph.labels φ).length)
    (ys : List Bool) : (body p skipSink right plan).HoareTime
      (EmitPred (word φ.encode) (bank i.val v j.val r a (20*j.val) f (levels φ) (varCount φ) g φ.length) ys)
      (EmitPred (word φ.encode) (bank i.val v (j.val+1) r a (20*(j.val+1)) f (levels φ) (varCount φ) g φ.length)
        (ys ++ fields φ i j p skipSink right plan r a)) (bodyBudget φ) := by
  have hj := j.isLt
  have hp := FormulaSwitchHeadPorts.hoare φ i j p skipSink right plan v r a f g (cap φ)
    (by unfold cap; omega) (by unfold cap; omega) (List.finRange 20) (20*j.val)
    (by simp only [List.length_finRange]; unfold cap; omega) ys
  simp only [List.length_finRange] at hp
  have hq := incRegTM_hoareTime (6 : Fin 20) j.val (word φ.encode)
    (bank i.val v j.val r a (20*j.val+20) f (levels φ) (varCount φ) g φ.length)
    (ys ++ fields φ i j p skipSink right plan r a) (word_parked _)
    (fun t _ => parked _ _ _ _ _ _ _ _ _ _ _ t) rfl
  have he : Function.update (bank i.val v j.val r a (20*j.val+20) f (levels φ) (varCount φ) g φ.length) 6 (regTape (j.val+1)) =
      bank i.val v (j.val+1) r a (20*(j.val+1)) f (levels φ) (varCount φ) g φ.length := by
    have hb : 20*j.val+20 = 20*(j.val+1) := by omega
    funext t; fin_cases t <;> simp [bank,FormulaSwitchVariableHeads.extend,
      FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,FormulaRailHeadVariables.extend,
      FormulaRailHeadPrepare.bank,hb]
  rw [he] at hq
  exact (seqTM_hoareTime _ _ hp (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _ _ _) _) hq).mono_bound
    (by unfold bodyBudget; omega)

def laterField (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V)
    (right : Bool) (plan : FormulaCoefficientPlan.Plan) (r a k : Nat) : List Bool :=
  if hk : k+1 < levels φ then fields φ i ⟨k+1,hk⟩ p false right plan r a else []

def laterBits (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V)
    (right : Bool) (plan : FormulaCoefficientPlan.Plan) (r a k : Nat) : List Bool :=
  (List.range k).flatMap (laterField φ i p right plan r a)

def loop (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 :=
  forRegTM (placeWorkTM 0 1 (body p false right plan)) 20

theorem loop_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V)
    (right : Bool) (plan : FormulaCoefficientPlan.Plan) (v r a f g : Nat)
    (hr : r ≤ (FormulaIndexedGraph.labels φ).length) (ha : a ≤ (FormulaIndexedGraph.labels φ).length)
    (ys : List Bool) : (loop p right plan).HoareTime
      (EmitPred (word φ.encode) (extend (bank i.val v 1 r a 20 f (levels φ) (varCount φ) g φ.length)
        (regTape (levels φ-1))) ys)
      (EmitPred (word φ.encode) (extend (bank i.val v (levels φ) r a (20*levels φ) f (levels φ) (varCount φ) g φ.length)
        (regTape (levels φ-1))) (ys ++ laterBits φ i p right plan r a (levels φ-1)))
      ((levels φ-1)*(bodyBudget φ+2)+(levels φ+1)) := by
  let L := levels φ
  let w := fun k => extend (bank i.val v (k+1) r a (20*(k+1)) f L (varCount φ) g φ.length) (regTape (L-1))
  let zs := fun k => ys ++ laterBits φ i p right plan r a k
  have h := forRegTM_hoareTime (placeWorkTM 0 1 (body p false right plan)) (20 : Fin 21)
    (L-1) (word φ.encode) w zs (bodyBudget φ) (word_parked _) (by intro k; rfl)
    (by intro k t _; exact FormulaChangingFrame.parked _ _ (parked _ _ _ _ _ _ _ _ _ _ _) (parked_regTape _) t) (by
      intro k hk
      have hkj : k+1 < levels φ := by dsimp only [L] at hk; omega
      let fuel : Tape := ⟨k+2,regCells (L-1)⟩
      have hfuel : Parked fuel := parked_regCells (by omega)
      have he (z : Nat) : Function.update (w z) 20 fuel =
          extend (bank i.val v (z+1) r a (20*(z+1)) f L (varCount φ) g φ.length) fuel := by
        funext t; fin_cases t <;> simp [w,extend]
      have hb := body_hoare φ i ⟨k+1,hkj⟩ p false right plan v r a f g hr ha (zs k)
      have hl := FormulaChangingFrame.append_hoare _ _ _ _ fuel _ _ _ (parked _ _ _ _ _ _ _ _ _ _ _) hfuel hb
      have hfield : laterField φ i p right plan r a k = fields φ i ⟨k+1,hkj⟩ p false right plan r a := by
        unfold laterField; split
        · rfl
        · next hn => exact (hn hkj).elim
      have hy : zs (k+1) = zs k ++ fields φ i ⟨k+1,hkj⟩ p false right plan r a := by
        simp [zs,laterBits,List.range_succ,List.flatMap_append,hfield,List.append_assoc]
      rw [he,he,hy]
      exact hl)
  have hL : L-1+1=L := by have := FormulaWiring.levels_pos φ; dsimp only [L]; omega
  have hL' : L-1+2=L+1 := by have := FormulaWiring.levels_pos φ; dsimp only [L]; omega
  simpa only [loop,w,zs,laterBits,List.range_zero,List.flatMap_nil,List.append_nil,
    Nat.zero_add,Nat.mul_one,hL,hL',L,Nat.add_assoc] using h

end UnconstrainedPACDetection.FormulaSwitchHeadLevels

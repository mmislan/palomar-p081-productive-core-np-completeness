module

public import proofs.UnconstrainedPACDetection.FormulaClauseSwitchCursor

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseTailHeads
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open FormulaChangingFrame (extend)

def frame (i c r a b L V C : Nat) (fuel : Tape) : Fin 21 → Tape :=
  extend (FormulaSwitchVariableHeads.extend (FormulaClauseHeadLoop.bank i c r a b L V C (regTape C))) fuel

theorem parked (i c r a b L V C : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ t, Parked (frame i c r a b L V C fuel t) :=
  FormulaChangingFrame.parked _ _ (FormulaSwitchVariableHeads.extend_parked _
    (FormulaClauseHeadLoop.parked _ _ _ _ _ _ _ _ _ (parked_regTape _))) hf

def route : Equiv.Perm (Fin 21) where
  toFun := ![0,1,2,3,4,9,10,11,12,13,5,6,7,8,14,15,16,17,18,19,20]
  invFun := ![0,1,2,3,4,10,11,12,13,5,6,7,8,9,14,15,16,17,18,19,20]
  left_inv := by intro t; fin_cases t <;> rfl
  right_inv := by intro t; fin_cases t <;> rfl

def query (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 :=
  VerifierWorkPermutation.machine (placeWorkTM 0 11 (FormulaClausePair.machine 2 false right plan)) route

def advance : TM 21 := seqTM (incRegTM 0) (iterTM (incRegTM 11) 20)

theorem advance_hoare (i c r a b L V C : Nat) (fuel : Tape) (hf : Parked fuel)
    (inp : Tape) (hi : Parked inp) (ys : List Bool) : advance.HoareTime
      (EmitPred inp (frame i c r a b L V C fuel) ys)
      (EmitPred inp (frame (i+1) c r a (b+20) L V C fuel) ys) (2*i+40*b+906) := by
  have h0 := incRegTM_hoareTime (0 : Fin 21) i inp (frame i c r a b L V C fuel) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ hf t) rfl
  have he0 : Function.update (frame i c r a b L V C fuel) 0 (regTape (i+1)) =
      frame (i+1) c r a b L V C fuel := by
    funext t; fin_cases t <;> simp [frame,extend,FormulaSwitchVariableHeads.extend,FormulaClauseHeadLoop.bank]
  rw [he0] at h0
  have h1 := iterTM_incRegTM_hoareTime (11 : Fin 21) 20 b inp (frame (i+1) c r a b L V C fuel) ys hi
    (parked _ _ _ _ _ _ _ _ _ hf) rfl
  have he1 : Function.update (frame (i+1) c r a b L V C fuel) 11 (regTape (b+20)) =
      frame (i+1) c r a (b+20) L V C fuel := by
    funext t; fin_cases t <;> simp [frame,extend,FormulaSwitchVariableHeads.extend,FormulaClauseHeadLoop.bank]
  rw [he1] at h1
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ hf) _) h1).mono_bound (by omega)

def body (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 := seqTM (query right plan) advance
def loop (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 := forRegTM (body right plan) 20

def field (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  if hk : k < levels φ then FormulaHeadFieldOrder.field φ right r a (FormulaClauseSwitchCursor.port φ ⟨k,hk⟩) else []

def bits (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  (List.range k).flatMap (field φ right r a)

def loopBudget (φ : SAT.CNF) : Nat :=
  levels φ*(20*φ.encode.length+6*φ.length+43*(FormulaIndexedGraph.labels φ).length+2*levels φ+1042)+(levels φ+2)

theorem loop_hoare (φ : SAT.CNF) (c : Fin φ.length) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.clause c.castSucc)) (ys : List Bool) :
    (loop right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (frame 0 c.val (index r) (index a) 2 (levels φ) (varCount φ) φ.length (regTape (levels φ))) ys)
      (EmitPred (word φ.encode) (frame (levels φ) c.val (index r) (index a) (20*levels φ+2)
        (levels φ) (varCount φ) φ.length (regTape (levels φ))) (ys ++ bits φ right r a (levels φ)))
      (loopBudget φ) := by
  let L := levels φ
  let N := (FormulaIndexedGraph.labels φ).length
  let w := fun k => frame k c.val (index r) (index a) (20*k+2) L (varCount φ) φ.length (regTape L)
  let zs := fun k => ys ++ bits φ right r a k
  have h := forRegTM_hoareTime (body right (choose right (tag r) (tag a) none)) (20 : Fin 21)
    L (word φ.encode) w zs (20*φ.encode.length+6*φ.length+43*N+2*L+1040) (word_parked _)
    (by intro k; rfl) (by intro k t _; exact parked _ _ _ _ _ _ _ _ _ (parked_regTape _) t) (by
      intro k hk
      let fuel : Tape := ⟨k+2,regCells L⟩
      have hfuel : Parked fuel := parked_regCells (by omega)
      have he (z : Nat) : Function.update (w z) 20 fuel =
          frame z c.val (index r) (index a) (20*z+2) L (varCount φ) φ.length fuel := by
        funext t; fin_cases t <;> simp [w,frame,extend]
      let b := FormulaClauseSwitchCursor.port φ ⟨k,hk⟩
      have hb : index b = 20*k+2 := FormulaClauseSwitchCursor.port_index φ ⟨k,hk⟩
      have ht : tag b = none := rfl
      have hq := FormulaClausePair.canonical_hoare φ ⟨k,hk⟩ c.castSucc 2 false right r a b ha
        (FormulaClauseSwitchCursor.port_meaning φ ⟨k,hk⟩) (zs k)
      rw [hb,ht] at hq
      have hquery := FormulaRoutedFrame.hoare _ 0 11 route _ _
        (frame k c.val (index r) (index a) (20*k+2) L (varCount φ) φ.length fuel) _ _ _
        (parked _ _ _ _ _ _ _ _ _ hfuel) (by
          intro t; fin_cases t <;> first | rfl | exact FormulaEndpointRegisters.unary_word 0) hq
      have hfield : field φ right r a k = FormulaHeadFieldOrder.field φ right r a b := by
        unfold field; split
        · rfl
        · next hn => exact (hn hk).elim
      change (query right (choose right (tag r) (tag a) none)).HoareTime _
        (EmitPred _ _ (zs k ++ FormulaHeadFieldOrder.field φ right r a b)) _ at hquery
      rw [← hfield] at hquery
      have hadv := advance_hoare k c.val (index r) (index a) (20*k+2) L (varCount φ) φ.length fuel hfuel
        (word φ.encode) (word_parked _) (zs k ++ field φ right r a k)
      have hs := seqTM_hoareTime _ _ hquery (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _ hfuel) _) hadv
      have hy : zs (k+1) = zs k ++ field φ right r a k := by
        simp [zs,bits,List.range_succ,List.flatMap_append,List.append_assoc]
      rw [he,he,hy]
      have hn := FormulaCoefficientRound.index_bound b
      rw [hb] at hn
      have hadd : 20*k+2+20 = 20*(k+1)+2 := by omega
      rw [hadd] at hs
      exact hs.mono_bound (by dsimp only [L,N] at *; have := c.isLt; omega))
  simpa only [loop,loopBudget,w,zs,bits,List.range_zero,List.flatMap_nil,List.append_nil,
    Nat.mul_zero,Nat.zero_add,L,N] using h

end UnconstrainedPACDetection.FormulaClauseTailHeads

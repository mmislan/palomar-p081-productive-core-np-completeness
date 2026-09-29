module

public import proofs.UnconstrainedPACDetection.FormulaVariableTailCaller

@[expose] public section

namespace UnconstrainedPACDetection.FormulaFinalVariableClauseLoop
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)

def bank (i c r a b L V C : Nat) (fuel : Tape) : Fin 20 → Tape :=
  ![regTape i,word [],word [],regTape c,word [],regTape V,regTape (L+1),word [],word [true],
    regTape r,regTape a,regTape b,word [],word [true],regTape (L+1),regTape L,regTape V,fuel,regTape C,word [true]]

theorem parked (i c r a b L V C : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ t, Parked (bank i c r a b L V C fuel t) := by
  intro t; fin_cases t
  all_goals first | exact parked_regTape _ | exact word_parked _ | exact hf

def route : Equiv.Perm (Fin 20) where
  toFun := ![0,16,1,8,3,2,4,13,9,10,11,7,19,5,6,12,14,15,17,18]
  invFun := ![0,2,5,4,6,13,14,11,3,8,9,10,15,7,16,17,1,18,19,12]
  left_inv := by intro t; fin_cases t <;> rfl
  right_inv := by intro t; fin_cases t <;> rfl

def round (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 20 :=
  VerifierWorkPermutation.machine (placeWorkTM 0 7
    (FormulaVariablePair.machine true false false right plan)) route

def advance : TM 20 := seqTM (incRegTM 3) (incRegTM 11)

theorem advance_hoare (i c r a b L V C : Nat) (fuel : Tape) (hf : Parked fuel)
    (inp : Tape) (hi : Parked inp) (ys : List Bool) : advance.HoareTime
    (EmitPred inp (bank i c r a b L V C fuel) ys)
    (EmitPred inp (bank i (c+1) r a (b+1) L V C fuel) ys) (2*c+2*b+9) := by
  have h1 := incRegTM_hoareTime (3 : Fin 20) c inp (bank i c r a b L V C fuel) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ hf t) rfl
  have he1 : Function.update (bank i c r a b L V C fuel) 3 (regTape (c+1)) =
      bank i (c+1) r a b L V C fuel := by
    funext t; fin_cases t <;> simp [bank]
  rw [he1] at h1
  have h2 := incRegTM_hoareTime (11 : Fin 20) b inp (bank i (c+1) r a b L V C fuel) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ hf t) rfl
  have he2 : Function.update (bank i (c+1) r a b L V C fuel) 11 (regTape (b+1)) =
      bank i (c+1) r a (b+1) L V C fuel := by
    funext t; fin_cases t <;> simp [bank]
  rw [he2] at h2
  exact (seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ hf) _) h2).mono_bound (by omega)

def body (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 20 :=
  seqTM (round right plan) advance

def machine (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 20 :=
  forRegTM (body right plan) 17

def field (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (c : Nat) : List Bool :=
  if hc : c < φ.length then
    let b := FormulaClauseCursor.port φ ⟨c,hc⟩
    if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ) (a,b)
    then BinaryFields.encodeField (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits
    else []
  else []

def bits (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  (List.range k).flatMap (field φ right r a)

/-- Physical internal-clause scan for the final variable tail. The merged final
    clause is handled separately; this phase also handles C=0. -/
theorem canonical_hoare (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var (Fin.last (varCount φ)))) (ys : List Bool) :
    (machine right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode)
        (bank (varCount φ) 0 (index r) (index a) (FormulaClauseCursor.base φ) (levels φ) (varCount φ)
          φ.length (regTape φ.length)) ys)
      (EmitPred (word φ.encode)
        (bank (varCount φ) φ.length (index r) (index a) (FormulaClauseCursor.base φ+φ.length)
          (levels φ) (varCount φ) φ.length (regTape φ.length))
        (ys ++ bits φ right r a φ.length))
      (φ.length*(10*varCount φ+10*φ.length+10*(FormulaIndexedGraph.labels φ).length+202)+(φ.length+2)) := by
  let C := φ.length
  let B := FormulaClauseCursor.base φ
  let N := (FormulaIndexedGraph.labels φ).length
  let w := fun k => bank (varCount φ) k (index r) (index a) (B+k) (levels φ) (varCount φ) C (regTape C)
  let zs := fun k => ys ++ bits φ right r a k
  have h := forRegTM_hoareTime (body right (choose right (tag r) (tag a) none))
    (17 : Fin 20) C (word φ.encode) w zs (10*varCount φ+10*C+10*N+200)
    (word_parked _) (by intro k; rfl)
    (by intro k t _; exact parked _ _ _ _ _ _ _ _ _ (parked_regTape C) t) (by
      intro k hk
      let fuel : Tape := ⟨k+2,regCells C⟩
      have hf : Parked fuel := parked_regCells (by omega)
      have he (z : Nat) : Function.update (w z) 17 fuel =
          bank (varCount φ) z (index r) (index a) (B+z) (levels φ) (varCount φ) C fuel := by
        funext t; fin_cases t <;> simp [w,bank]
      let b := FormulaClauseCursor.port φ ⟨k,hk⟩
      have hb : index b = B+k := FormulaClauseCursor.port_index φ ⟨k,hk⟩
      have ht : tag b = none := rfl
      have hq := FormulaVariablePair.clause_entry φ (Fin.last (varCount φ)) ⟨k,by omega⟩ right r a b ha
        (FormulaClauseCursor.port_meaning φ ⟨k,hk⟩) (zs k)
      rw [hb,ht] at hq
      have hr := FormulaRoutedFrame.hoare _ 0 7 route _ _
        (bank (varCount φ) k (index r) (index a) (B+k) (levels φ) (varCount φ) C fuel) _ _ _
        (parked _ _ _ _ _ _ _ _ _ hf) (by
          intro t; fin_cases t <;> first
          | rfl
          | exact FormulaEndpointRegisters.unary_word 0) hq
      have hfield : field φ right r a k =
          if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
            (FormulaIndexedGraph.terminals φ) (a,b) then BinaryFields.encodeField
              (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits
          else [] := by
        unfold field; split
        · rfl
        · next hn => exact (hn hk).elim
      rw [← hfield] at hr
      have hs := seqTM_hoareTime _ _ hr
        (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _ hf) _)
        (advance_hoare (varCount φ) k (index r) (index a) (B+k) (levels φ) (varCount φ) C fuel hf
          (word φ.encode) (word_parked _) (zs k ++ field φ right r a k))
      have hy : zs (k+1) = zs k ++ field φ right r a k := by
        simp [zs,bits,List.range_succ,List.flatMap_append,List.append_assoc]
      rw [he,he,hy]
      have hn := FormulaCoefficientRound.index_bound b
      rw [hb] at hn
      have hadd : B+k+1 = B+(k+1) := by omega
      rw [hadd] at hs
      have hrb := FormulaCoefficientRound.index_bound r
      have hab := FormulaCoefficientRound.index_bound a
      exact hs.mono_bound (by
        dsimp only [N,C] at *
        simp only [Fin.val_last] at hs
        cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hs ⊢ <;>
          omega))
  simpa only [machine,round,w,zs,bits,List.range_zero,List.flatMap_nil,List.append_nil,
    Nat.add_zero,C,B,N,Nat.add_assoc] using h

end UnconstrainedPACDetection.FormulaFinalVariableClauseLoop

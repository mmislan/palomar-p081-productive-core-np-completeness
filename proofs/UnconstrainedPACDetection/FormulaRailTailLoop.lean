module

public import proofs.UnconstrainedPACDetection.FormulaRailTailCanonical

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailTailLoop
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)
open FormulaRailHeadVariables (extend extend_parked)

def bank (k v r A L V : Nat) (fuel : Tape) : Fin 18 → Tape :=
  extend (FormulaRailHeadPrepare.bank k v k r (A+k) (A+k) v L V) fuel

theorem parked (k v r A L V : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ t, Parked (bank k v r A L V fuel t) :=
  extend_parked _ _ (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) hf

def advance : TM 18 := seqTM (incRegTM 0) (incRegTM 10)

theorem advance_hoare (k v r A L V : Nat) (fuel : Tape) (hf : Parked fuel)
    (inp : Tape) (hi : Parked inp) (ys : List Bool) : advance.HoareTime
      (EmitPred inp (extend (FormulaRailHeadPrepare.bank k v (k+1) r (A+k) (A+k+1) v L V) fuel) ys)
      (EmitPred inp (bank (k+1) v r A L V fuel) ys) (2*k+2*(A+k)+9) := by
  let w := extend (FormulaRailHeadPrepare.bank k v (k+1) r (A+k) (A+k+1) v L V) fuel
  let z := extend (FormulaRailHeadPrepare.bank (k+1) v (k+1) r (A+k) (A+k+1) v L V) fuel
  have h0 := incRegTM_hoareTime (0 : Fin 18) k inp w ys hi
    (fun t _ => extend_parked _ _ (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) hf t) rfl
  have he0 : Function.update w 0 (regTape (k+1)) = z := by
    funext t; fin_cases t <;> simp [w,z,extend,FormulaRailHeadPrepare.bank]
  rw [he0] at h0
  have h1 := incRegTM_hoareTime (10 : Fin 18) (A+k) inp z ys hi
    (fun t _ => extend_parked _ _ (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) hf t) rfl
  have he1 : Function.update z 10 (regTape (A+k+1)) = bank (k+1) v r A L V fuel := by
    funext t; fin_cases t <;> simp [z,bank,extend,FormulaRailHeadPrepare.bank,Nat.add_assoc]
  rw [he1] at h1
  exact (seqTM_hoareTime _ _ h0
    (emitPred_transition hi (extend_parked _ _ (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) hf) _) h1).mono_bound (by omega)

def body (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 18 :=
  seqTM (placeWorkTM 0 1 (FormulaRailTailMiddle.machine s right plan)) advance

def fields (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  if hk : k < levels φ then
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaHeadFieldOrder.field φ right r (FormulaRailCursor.port φ v s ⟨k,by omega⟩))
  else []

def bits (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  (List.range k).flatMap (fields φ v s right r)

def roundBudget (φ : SAT.CNF) : Nat :=
  8*opBudget (cap φ)+48*φ.encode.length+55*varCount φ+12*levels φ+
    8*(FormulaIndexedGraph.labels φ).length+537

theorem body_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (v : Fin (varCount φ)) (s right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    (body s right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val (index r)
        (FormulaRailBase.value (levels φ) (varCount φ) v.val s) (levels φ) (varCount φ) fuel) ys)
      (EmitPred (word φ.encode) (bank (i.val+1) v.val (index r)
        (FormulaRailBase.value (levels φ) (varCount φ) v.val s) (levels φ) (varCount φ) fuel)
        (ys ++ fields φ v s right r i.val)) (roundBudget φ) := by
  let a := FormulaRailCursor.port φ v s i.castSucc
  let A := FormulaRailBase.value (levels φ) (varCount φ) v.val s
  have ha : tailMeaning φ a = .inr (.rail v s i.castSucc) := by
    simp [a,tailMeaning,FormulaRailCursor.port,tailVertex,MarkedGraph.decode]
  have ht : tag a = none := rfl
  have hai : index a = A+i.val := by
    obtain ⟨pre,post,hp,hl⟩ := FormulaRailBase.factor φ v s
    simpa [a,A,hl] using FormulaRailCursor.port_index φ v s pre post hp i.castSucc
  have hi := i.isLt
  have hv := v.isLt
  obtain ⟨hL,hV,_⟩ := FormulaEnumeration.parameter_bounds φ
  have hN : (FormulaIndexedGraph.labels φ).length ≤ cap φ := by
    apply (FormulaIndexedGraph.labels_bound φ).trans
    unfold cap; nlinarith only [Nat.zero_le φ.encode.length]
  have hAi : A+i.val ≤ (FormulaIndexedGraph.labels φ).length := by
    rw [← hai]; exact FormulaCoefficientRound.index_bound a
  have h := FormulaRailTailCanonical.middle_hoare φ i v s right r a ha i.val (A+i.val) v.val ys
    (by unfold cap; nlinarith) (hAi.trans hN) (by unfold cap; nlinarith)
  rw [ht,hai] at h
  have hfld : fields φ v s right r i.val =
      (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
        (FormulaHeadFieldOrder.field φ right r a) := by
    unfold fields; rw [dite_eq_left hi]
    rfl
  rw [← hfld] at h
  have h0 := FormulaRailHeadVariables.lift_hoare _ _ _ _ fuel _ _ _
    (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) hf h
  have h1 := advance_hoare i.val v.val (index r) A (levels φ) (varCount φ) fuel hf
    (word φ.encode) (word_parked _) (ys ++ fields φ v s right r i.val)
  exact (seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (extend_parked _ _ (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) hf) _) h1).mono_bound
      (by unfold roundBudget; omega)

def machine (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 18 :=
  forRegTM (body s right plan) 17

theorem loop_hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine s right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (bank 0 v.val (index r)
        (FormulaRailBase.value (levels φ) (varCount φ) v.val s)
        (levels φ) (varCount φ) (regTape (levels φ))) ys)
      (EmitPred (word φ.encode) (bank (levels φ) v.val (index r)
        (FormulaRailBase.value (levels φ) (varCount φ) v.val s)
        (levels φ) (varCount φ) (regTape (levels φ)))
        (ys ++ bits φ v s right r (levels φ)))
      (levels φ*(roundBudget φ+2)+(levels φ+2)) := by
  let A := FormulaRailBase.value (levels φ) (varCount φ) v.val s
  let L := levels φ
  let w := fun k => bank k v.val (index r) A L (varCount φ) (regTape L)
  let zs := fun k => ys ++ bits φ v s right r k
  have h := forRegTM_hoareTime (body s right (choose right (tag r) none none))
    (17 : Fin 18) L (word φ.encode) w zs (roundBudget φ) (word_parked _)
    (by intro k; rfl) (by intro k t _; exact parked _ _ _ _ _ _ _ (parked_regTape _) t) (by
      intro k hk
      let fuel : Tape := ⟨k+2,regCells L⟩
      have hf : Parked fuel := parked_regCells (by omega)
      have he (z : Nat) : Function.update (w z) 17 fuel = bank z v.val (index r) A L (varCount φ) fuel := by
        funext t; fin_cases t <;> simp [w,bank,extend]
      have hb := body_hoare φ ⟨k,hk⟩ v s right r fuel hf (zs k)
      have hy : zs (k+1) = zs k ++ fields φ v s right r k := by
        simp [zs,bits,List.range_succ,List.flatMap_append,List.append_assoc]
      rw [he,he,hy]
      exact hb)
  simpa only [machine,w,zs,bits,List.range_zero,List.flatMap_nil,List.append_nil,L,A,Nat.add_assoc] using h

end UnconstrainedPACDetection.FormulaRailTailLoop

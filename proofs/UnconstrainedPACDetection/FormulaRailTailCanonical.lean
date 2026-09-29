module

public import proofs.UnconstrainedPACDetection.FormulaRailEndPrepare

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailTailCanonical
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning headMeaning)
open FormulaRailHeadPrepare (bank parked)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)
open FormulaHeadFieldOrder (field)

theorem middle_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (v : Fin (varCount φ)) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.rail v s i.castSucc)) (j b f : Nat) (ys : List Bool)
    (hj : j ≤ cap φ) (hb : b ≤ cap φ) (hf : f ≤ cap φ) :
    (FormulaRailTailMiddle.machine s right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val j (index r) (index a) b f (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (bank i.val v.val (i.val+1) (index r) (index a) (index a+1) v.val
        (levels φ) (varCount φ))
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (field φ right r a)))
      (8*opBudget (cap φ)+48*φ.encode.length+55*v.val+10*i.val+
        6*(FormulaIndexedGraph.labels φ).length+527) := by
  have h := FormulaRailTailMiddle.hoare φ i v s right r a ha j b f ys hj hb hf
  rw [List.append_assoc,FormulaUniqueHead.middle_bits φ i v s right r a ha] at h
  exact h

theorem endpoint_next (φ : SAT.CNF) (v : Fin (varCount φ)) (s : Bool)
    (a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.rail v s (Fin.last (levels φ)))) (y : FormulaWiring.Vertex φ) :
    FormulaWiring.adjacency φ (tailMeaning φ a) y ↔
      y=headMeaning φ (FormulaVariableCursor.port φ v.succ) := by
  rw [ha,FormulaOutdegree.rail_iff,FormulaVariableCursor.port_meaning]
  simp [FormulaOutdegree.railNext]
  rfl

theorem endpoint_emit (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.rail v s (Fin.last (levels φ)))) (f : Nat) (ys : List Bool) :
    (FormulaVariableTailHeads.emit right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank (levels φ) v.val (levels φ) (index r) (index a)
        (20*levels φ+v.val+1) f (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (bank (levels φ) v.val (levels φ) (index r) (index a)
        (20*levels φ+v.val+1) f (levels φ) (varCount φ))
        (ys ++ field φ right r a (FormulaVariableCursor.port φ v.succ)))
      (3*(FormulaIndexedGraph.labels φ).length+27) := by
  let b := FormulaVariableCursor.port φ v.succ
  have hb : index b = 20*levels φ+v.val+1 := by
    simpa [b,Nat.add_assoc] using FormulaVariableCursor.port_index φ v.succ
  have ht : tag b = none := rfl
  have he : FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,b) := by
    rw [FormulaHeadFieldOrder.arc_meaning,endpoint_next φ v s a ha]
  have h := FormulaCoefficientRound.arc_hoare (FormulaIndexedGraph.edge φ)
    (FormulaIndexedGraph.terminals φ) right r ⟨(a,b),he⟩ ys (word φ.encode) (word_parked _)
  have hf : field φ right r a b = BinaryFields.encodeField
      (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits := ite_eq_left he
  rw [← hf,hb,ht] at h
  exact FormulaRoutedFrame.hoare _ 0 12 FormulaVariableTailHeads.route _ _ _ _ _ _
    (parked _ _ _ _ _ _ _ _ _) (by intro t; fin_cases t <;> rfl) h

def endpoint (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 17 :=
  seqTM FormulaRailEndPrepare.machine (FormulaVariableTailHeads.emit right plan)

theorem endpoint_hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.rail v s (Fin.last (levels φ)))) (j b f : Nat) (ys : List Bool)
    (hj : j ≤ cap φ) (hb : b ≤ cap φ) :
    (endpoint right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank (levels φ) v.val j (index r) (index a) b f (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (bank (levels φ) v.val (levels φ) (index r) (index a)
        (20*levels φ+v.val+1) f (levels φ) (varCount φ))
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (field φ right r a)))
      (5*opBudget (cap φ)+3*(FormulaIndexedGraph.labels φ).length+32) := by
  have hN : (FormulaIndexedGraph.labels φ).length ≤ cap φ := by
    apply (FormulaIndexedGraph.labels_bound φ).trans
    unfold cap
    nlinarith only [Nat.zero_le φ.encode.length]
  obtain ⟨hL,hV,_⟩ := FormulaEnumeration.parameter_bounds φ
  have hv := v.isLt
  have hbase : 20*levels φ+v.val+1 ≤ cap φ := by
    have h := FormulaCoefficientRound.index_bound (FormulaVariableCursor.port φ v.succ)
    rw [FormulaVariableCursor.port_index] at h
    exact (by simpa [Nat.add_assoc] using h : 20*levels φ+v.val+1 ≤ (FormulaIndexedGraph.labels φ).length).trans hN
  have h0 := FormulaRailEndPrepare.hoare (levels φ) v.val j (index r) (index a) b f
    (levels φ) (varCount φ) (cap φ) (word φ.encode) (word_parked _) ys
    (by unfold cap; nlinarith only [Nat.zero_le φ.encode.length])
    (by unfold cap; nlinarith) (by unfold cap; nlinarith) hj hb hbase
  have h1 := endpoint_emit φ v s right r a ha f ys
  have h := seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _) _) h1
  rw [← FormulaUniqueHead.canonical φ right r a _ (endpoint_next φ v s a ha)] at h
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.FormulaRailTailCanonical

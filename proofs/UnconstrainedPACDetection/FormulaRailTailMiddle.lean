module

public import proofs.UnconstrainedPACDetection.FormulaRailTailSuccessorPrepare

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailTailMiddle
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open FormulaRailHeadPrepare (bank parked)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)
open FormulaRailTailCandidates (switchPort switchQuery successorQuery)
open FormulaHeadFieldOrder (field)

def machine (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 17 :=
  seqTM FormulaRailTailPrepare.machine (seqTM (switchQuery s right plan)
    (seqTM FormulaRailTailSuccessorPrepare.machine (successorQuery s right plan)))

theorem hoare (φ : SAT.CNF) (i : Fin (levels φ)) (v : Fin (varCount φ)) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.rail v s i.castSucc)) (j b f : Nat) (ys : List Bool)
    (hj : j ≤ cap φ) (hb : b ≤ cap φ) (hf : f ≤ cap φ) :
    (machine s right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val j (index r) (index a) b f (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (bank i.val v.val (i.val+1) (index r) (index a) (index a+1) v.val
        (levels φ) (varCount φ))
        (ys ++ field φ right r a (switchPort φ i) ++ field φ right r a (FormulaRailCursor.port φ v s i.succ)))
      (8*opBudget (cap φ)+48*φ.encode.length+55*v.val+10*i.val+
        6*(FormulaIndexedGraph.labels φ).length+527) := by
  have hN : (FormulaIndexedGraph.labels φ).length ≤ cap φ := by
    apply (FormulaIndexedGraph.labels_bound φ).trans
    unfold cap
    nlinarith only [Nat.zero_le φ.encode.length]
  have h20 : 20 ≤ cap φ := by unfold cap; nlinarith only [Nat.zero_le φ.encode.length]
  obtain ⟨hL,hV,_⟩ := FormulaEnumeration.parameter_bounds φ
  have hi0 := i.isLt
  have hv0 := v.isLt
  have hiM : i.val ≤ cap φ := by unfold cap; nlinarith
  have hvM : v.val ≤ cap φ := by unfold cap; nlinarith
  have hbase : 20*i.val+3 ≤ cap φ := by
    have h := FormulaCoefficientRound.index_bound (switchPort φ i)
    rw [FormulaRailTailCandidates.switch_index] at h
    exact h.trans hN
  have haM : index a ≤ cap φ := (FormulaCoefficientRound.index_bound a).trans hN
  have h0 := FormulaRailTailPrepare.hoare i.val v.val j (index r) (index a) b f (levels φ)
    (varCount φ) (cap φ) (word φ.encode) (word_parked _) ys h20 hiM hj hb hbase
  have h1 := FormulaRailTailCandidates.switch_hoare φ i v s right r a ha f ys
  have h2 := FormulaRailTailSuccessorPrepare.hoare i.val v.val (index r) (index a) (20*i.val+3) f
    (levels φ) (varCount φ) (cap φ) (word φ.encode) (word_parked _)
    (ys ++ field φ right r a (switchPort φ i)) hiM hvM haM hbase hf
  have h3 := FormulaRailTailCandidates.successor_hoare φ i v s right r a ha
    (ys ++ field φ right r a (switchPort φ i))
  have h23 := seqTM_hoareTime _ _ h2
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _) _) h3
  have h123 := seqTM_hoareTime _ _ h1
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _) _) h23
  exact (seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _) _) h123).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaRailTailMiddle

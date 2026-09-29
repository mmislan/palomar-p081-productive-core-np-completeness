module

public import proofs.UnconstrainedPACDetection.FormulaRailTailLoop

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailTailBlock
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)
open FormulaRailHeadVariables (extend extend_parked)

def bits (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : List Bool :=
  (List.finRange (levels φ+1)).flatMap (fun j =>
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaHeadFieldOrder.field φ right r (FormulaRailCursor.port φ v s j)))

theorem bits_eq (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    FormulaRailTailLoop.bits φ v s right r (levels φ) ++
      (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
        (FormulaHeadFieldOrder.field φ right r (FormulaRailCursor.port φ v s (Fin.last (levels φ)))) =
      bits φ v s right r := by
  have hr := FormulaHeadFieldOrder.range_fields (levels φ) (fun i =>
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaHeadFieldOrder.field φ right r (FormulaRailCursor.port φ v s i.castSucc)))
  change FormulaRailTailLoop.bits φ v s right r (levels φ) = _ at hr
  unfold bits
  rw [hr,List.finRange_succ_last]
  simp only [List.flatMap_append,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,List.append_nil]

def machine (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 18 :=
  seqTM (FormulaRailTailLoop.machine s right plan)
    (placeWorkTM 0 1 (FormulaRailTailCanonical.endpoint right plan))

def budget (φ : SAT.CNF) : Nat :=
  levels φ*(FormulaRailTailLoop.roundBudget φ+2)+(levels φ+2)+
    5*opBudget (cap φ)+3*(FormulaIndexedGraph.labels φ).length+33

theorem canonical_hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine s right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (FormulaRailTailLoop.bank 0 v.val (index r)
        (FormulaRailBase.value (levels φ) (varCount φ) v.val s)
        (levels φ) (varCount φ) (regTape (levels φ))) ys)
      (EmitPred (word φ.encode)
        (extend (FormulaRailHeadPrepare.bank (levels φ) v.val (levels φ) (index r)
          (FormulaRailBase.value (levels φ) (varCount φ) v.val s+levels φ)
          (20*levels φ+v.val+1) v.val (levels φ) (varCount φ)) (regTape (levels φ)))
        (ys ++ bits φ v s right r)) (budget φ) := by
  let a := FormulaRailCursor.port φ v s (Fin.last (levels φ))
  let A := FormulaRailBase.value (levels φ) (varCount φ) v.val s
  have ha : tailMeaning φ a = .inr (.rail v s (Fin.last (levels φ))) := by
    simp [a,tailMeaning,FormulaRailCursor.port,tailVertex,MarkedGraph.decode]
  have ht : tag a = none := rfl
  have hai : index a = A+levels φ := by
    obtain ⟨pre,post,hp,hl⟩ := FormulaRailBase.factor φ v s
    simpa [a,A,hl] using FormulaRailCursor.port_index φ v s pre post hp (Fin.last (levels φ))
  have hN : (FormulaIndexedGraph.labels φ).length ≤ cap φ := by
    apply (FormulaIndexedGraph.labels_bound φ).trans
    unfold cap; nlinarith only [Nat.zero_le φ.encode.length]
  have hA : A+levels φ ≤ cap φ := by
    rw [← hai]; exact (FormulaCoefficientRound.index_bound a).trans hN
  have hL : levels φ ≤ cap φ := by
    have h := (FormulaEnumeration.parameter_bounds φ).1
    unfold cap; nlinarith
  have h0 := FormulaRailTailLoop.loop_hoare φ v s right r ys
  have h1 := FormulaRailTailCanonical.endpoint_hoare φ v s right r a ha (levels φ) (A+levels φ) v.val
    (ys ++ FormulaRailTailLoop.bits φ v s right r (levels φ)) hL hA
  rw [ht,hai] at h1
  have h1' := FormulaRailHeadVariables.lift_hoare _ _ _ _ (regTape (levels φ)) _ _ _
    (FormulaRailHeadPrepare.parked _ _ _ _ _ _ _ _ _) (parked_regTape _) h1
  have h := seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (FormulaRailTailLoop.parked _ _ _ _ _ _ _ (parked_regTape _)) _) h1'
  rw [List.append_assoc,bits_eq φ v s right r] at h
  exact h.mono_bound (by unfold budget; omega)

end UnconstrainedPACDetection.FormulaRailTailBlock

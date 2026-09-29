module

public import proofs.UnconstrainedPACDetection.FormulaFinalVariablePrepare

@[expose] public section

namespace UnconstrainedPACDetection.FormulaFinalVariableCanonical
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open FormulaVertexHeadFields (vertex)
open FormulaHeadFieldOrder (field)
open FormulaFinalVariableClauseLoop (bank parked bits)
open VerifierPairRestore (word word_parked)

theorem vertex_eq (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var (Fin.last (varCount φ)))) (x : FormulaWiring.Vertex φ) :
    vertex φ right r a x = match x with
      | .inr (.clause c) => vertex φ right r a (.inr (.clause c))
      | _ => [] := by
  cases x with
  | inl x =>
    apply FormulaClauseTailCanonical.vertex_zero
    rw [ha]
    simp [FormulaWiring.adjacency,SwitchStack.Edge,SwitchStack.sw,FormulaWiring.DataWire]
  | inr x =>
    cases x with
    | clause c => rfl
    | var v =>
      apply FormulaClauseTailCanonical.vertex_zero
      rw [ha]
      simp [FormulaWiring.adjacency,SwitchStack.Edge,FormulaWiring.DataWire]
    | rail v s j =>
      apply FormulaClauseTailCanonical.vertex_zero
      rw [ha]
      have hv := v.isLt
      simp [FormulaWiring.adjacency,SwitchStack.Edge,FormulaWiring.DataWire]
      omega

theorem bits_eq (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var (Fin.last (varCount φ)))) :
    field φ right r a (.inl false) ++ bits φ right r a φ.length =
      (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (field φ right r a) := by
  have hn {X : Type} (xs : List X) : xs.flatMap (fun _ => ([] : List Bool)) = [] :=
    List.flatMap_eq_nil_iff.mpr (by intro x hx; rfl)
  have hz : (FormulaClauseCursor.initialVertices φ).flatMap (vertex φ right r a) = [] := by
    simp only [FormulaClauseCursor.initialVertices,List.flatMap_append,List.flatMap_assoc,List.flatMap_map,
      vertex_eq φ right r a ha,SwitchStack.sw,hn,List.nil_append]
  have hl := congrArg (fun xs => xs.flatMap (vertex φ right r a)) (FormulaClauseCursor.labels φ)
  rw [List.flatMap_append,hz,List.nil_append] at hl
  have hc := FormulaOtherHeadOrder.clause_fields φ right r a
  change (FormulaOtherHeadOrder.clauses φ).flatMap (vertex φ right r a) =
    bits φ right r a φ.length at hc
  change (FormulaIndexedGraph.labels φ).flatMap (vertex φ right r a) =
    (FormulaOtherHeadOrder.clauses φ).flatMap (vertex φ right r a) at hl
  rw [hc] at hl
  have hm : FormulaMergedHeads.field φ right r a true = [] := by
    change field φ right r a (.inl true) = []
    unfold field
    apply ite_eq_right
    rw [FormulaHeadFieldOrder.arc_meaning,ha,FormulaMergedHeads.merged_meaning]
    simp [FormulaWiring.sinkQ,FormulaWiring.adjacency,SwitchStack.Edge,SwitchStack.sw,FormulaWiring.DataWire]
  have hh := FormulaVertexHeadFields.head_scan φ right r a
  rw [hl,hm,List.append_nil] at hh
  exact hh.symm

def machine (right : Bool) (merged ordinary : FormulaCoefficientPlan.Plan) : TM 20 :=
  seqTM (FormulaFinalVariableMerged.machine right merged)
    (seqTM FormulaFinalVariablePrepare.machine (FormulaFinalVariableClauseLoop.machine right ordinary))

theorem canonical_hoare (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var (Fin.last (varCount φ)))) (c b f : Nat) (ys : List Bool) :
    (machine right (choose right (tag r) (tag a) (some false))
      (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank (varCount φ) c (index r) (index a) b
        (levels φ) (varCount φ) φ.length (regTape f)) ys)
      (EmitPred (word φ.encode) (bank (varCount φ) φ.length (index r) (index a)
        (FormulaClauseCursor.base φ+φ.length) (levels φ) (varCount φ) φ.length (regTape φ.length))
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (field φ right r a)))
      (40*(opBudget (FormulaVariableTailBound.cap φ)+1)+2*c+2*b+2*f+4*φ.length^2+23*φ.length+
        7*varCount φ+3*(FormulaIndexedGraph.labels φ).length+131+
        φ.length*(10*varCount φ+10*φ.length+10*(FormulaIndexedGraph.labels φ).length+202)+(φ.length+2)) := by
  have h0 := FormulaFinalVariableMerged.hoare φ right r a ha c b (regTape f) (parked_regTape _) ys
  have h1 := FormulaFinalVariablePrepare.hoare φ (varCount φ) φ.length (index r) (index a) 0 f
    (ys ++ field φ right r a (.inl false)) (Nat.zero_le _)
  have h2 := FormulaFinalVariableClauseLoop.canonical_hoare φ right r a ha
    (ys ++ field φ right r a (.inl false))
  have h12 := seqTM_hoareTime _ _ h1
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) h2
  have h := seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) h12
  rw [List.append_assoc,bits_eq φ right r a ha] at h
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.FormulaFinalVariableCanonical

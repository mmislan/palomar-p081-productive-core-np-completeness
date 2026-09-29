module

public import proofs.UnconstrainedPACDetection.FormulaMergedTails

@[expose] public section

namespace UnconstrainedPACDetection.FormulaAllTails
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaVariableTailBound (cap)

def frame (r L V C : Nat) : Fin 22 → Tape := FormulaExternalTailPhase.frame 0 r L V C V C

theorem parked (r L V C : Nat) : ∀ t, Parked (frame r L V C t) :=
  FormulaExternalTailPhase.parked _ _ _ _ _ _ _

theorem finish_hoare (r L V C : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    (clearRegTM (5 : Fin 22)).HoareTime
      (EmitPred inp (FormulaExternalTailPhase.frame V r L V C V C) ys)
      (EmitPred inp (frame r L V C) ys) (2*V+4) := by
  have h := clearRegTM_hoareTime (5 : Fin 22) V inp (FormulaExternalTailPhase.frame V r L V C V C) ys hi
    (fun t _ => FormulaExternalTailPhase.parked _ _ _ _ _ _ _ t) rfl
  have he : Function.update (FormulaExternalTailPhase.frame V r L V C V C) 5 (regTape 0) = frame r L V C := by
    funext t; fin_cases t <;> simp [frame,FormulaExternalTailPhase.frame,FormulaAllRailTails.frame,
      FormulaChangingFrame.extend,FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,
      FormulaRailTailReentrant.frame,FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he] at h
  exact h

def machine (right : Bool) (rt : Option Bool) : TM 22 :=
  seqTM (placeWorkTM 0 1 (FormulaMergedTails.machine right rt))
    (seqTM (FormulaSwitchTailPhase.machine right rt)
      (seqTM (FormulaExternalTailPhase.machine right (choose right rt none none) (choose right rt none (some false)))
        (clearRegTM 5)))

def budget (φ : SAT.CNF) : Nat := FormulaMergedTails.budget φ+FormulaSwitchTailPhase.budget φ+
  FormulaExternalTailPhase.budget φ+2*varCount φ+7

theorem order (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    FormulaVertexTailFields.port φ right r (.inl false) ++ FormulaVertexTailFields.port φ right r (.inl true) ++
      ((List.finRange (levels φ)).flatMap (fun i => (List.finRange 20).map (SwitchStack.sw i))).flatMap
        (FormulaVertexTailFields.vertex φ right r) ++ FormulaExternalTailPhase.bits φ right r =
      (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (FormulaVertexTailFields.port φ right r) := by
  have hv := congrArg (fun xs => xs.flatMap (FormulaVertexTailFields.vertex φ right r))
    (FormulaOrderedEnumeration.labels_eq_vertices φ)
  rw [FormulaVertexTailFields.tail_scan,hv]
  simp only [FormulaEnumeration.vertices,FormulaExternalTailPhase.bits,FormulaExternalTailPhase.vertices,
    FormulaOtherHeadOrder.variableHeads,FormulaOtherHeadOrder.rails,FormulaOtherHeadOrder.clauses,
    List.flatMap_append,List.append_assoc]

theorem canonical_hoare (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine right (tag r)).HoareTime
      (EmitPred (word φ.encode) (frame (index r) (levels φ) (varCount φ) φ.length) ys)
      (EmitPred (word φ.encode) (frame (index r) (levels φ) (varCount φ) φ.length)
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
          (FormulaVertexTailFields.port φ right r))) (budget φ) := by
  have hV : varCount φ ≤ cap φ := by
    have h := (FormulaEnumeration.parameter_bounds φ).2.1
    unfold cap; nlinarith
  have hC : φ.length ≤ cap φ := by
    have h := (FormulaEnumeration.parameter_bounds φ).2.2
    unfold cap; nlinarith
  have h0 := FormulaMergedTails.hoare φ right r ys
  have h0' := FormulaChangingFrame.append_hoare _ _ _ _ (regTape φ.length) _ _ _
    (FormulaSwitchTailReentrant.parked _ _ _ _ _ _) (parked_regTape _) h0
  let zs := ys ++ FormulaVertexTailFields.port φ right r (.inl false) ++ FormulaVertexTailFields.port φ right r (.inl true)
  have h1 := FormulaSwitchTailPhase.canonical_hoare φ right r zs
  let ts := zs ++ ((List.finRange (levels φ)).flatMap (fun i => (List.finRange 20).map (SwitchStack.sw i))).flatMap
    (FormulaVertexTailFields.vertex φ right r)
  have h2 := FormulaExternalTailPhase.canonical_hoare φ right r 0 (varCount φ) φ.length ts (Nat.zero_le _) hV hC
  have h3 := finish_hoare (index r) (levels φ) (varCount φ) φ.length (word φ.encode) (word_parked _)
    (ts ++ FormulaExternalTailPhase.bits φ right r)
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition (word_parked _) (FormulaExternalTailPhase.parked _ _ _ _ _ _ _) _) h3
  have h123 := seqTM_hoareTime _ _ h1 (emitPred_transition (word_parked _) (parked _ _ _ _) _) h23
  have h := seqTM_hoareTime _ _ h0' (emitPred_transition (word_parked _) (parked _ _ _ _) _) h123
  have he : ts ++ FormulaExternalTailPhase.bits φ right r = ys ++
      (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (FormulaVertexTailFields.port φ right r) := by
    have ho := order φ right r
    simpa only [ts,zs,List.append_assoc] using congrArg (fun z => ys ++ z) ho
  rw [he] at h
  exact h.mono_bound (by unfold budget; omega)

end UnconstrainedPACDetection.FormulaAllTails

module

public import proofs.UnconstrainedPACDetection.FormulaRowLoop
public import proofs.UnconstrainedPACDetection.FormulaOrderedSchedule

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRows
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (tag index)

def row (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : List Bool :=
  (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (FormulaVertexTailFields.port φ right r)

def bits (φ : SAT.CNF) (right : Bool) : List Bool :=
  (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (row φ right)

theorem order (φ : SAT.CNF) (right : Bool) : bits φ right =
    row φ right (.inl false) ++ row φ right (.inl true) ++
      FormulaRowLoop.bits φ right (FormulaIndexedGraph.labels φ).length := by
  have hs := FormulaHeadFieldOrder.selected_fields (List.finRange (FormulaIndexedGraph.labels φ).length)
    (fun k => k ∉ Set.range (FormulaIndexedGraph.terminals φ)) (List.nodup_finRange _)
    (fun k => row φ right (.inr k)) (FormulaRowGate.field φ right)
    (by intro k; unfold FormulaRowGate.field; rw [dite_eq_left k.property]; rfl)
    (by intro k hk; unfold FormulaRowGate.field; rw [dite_eq_right hk])
  change (FiniteMarkedSource.internals (FormulaIndexedGraph.terminals φ)).flatMap
    (fun k => row φ right (.inr k)) = _ at hs
  have hr := FormulaHeadFieldOrder.range_fields (FormulaIndexedGraph.labels φ).length (FormulaRowGate.field φ right)
  change FormulaRowLoop.bits φ right (FormulaIndexedGraph.labels φ).length = _ at hr
  rw [← hr] at hs
  simpa only [bits,FormulaOrderedTable.rows,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.flatMap_map,List.append_assoc] using
      congrArg (fun z => row φ right (.inl false) ++ row φ right (.inl true) ++ z) hs

theorem scan_bits (φ : SAT.CNF) (right : Bool) : bits φ right =
    (FormulaOrderedSchedule.scan (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ) right).flatMap
      (fun z => BinaryFields.encodeField z.bits) := by
  unfold bits row FormulaVertexTailFields.port FormulaOrderedSchedule.scan
  simp only [List.flatMap_assoc]
  apply congrArg (fun f => (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap f)
  funext r
  apply congrArg (fun f => (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap f)
  funext a
  apply congrArg (fun f => (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap f)
  funext b
  by_cases h : FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ) (a,b)
  · simp [FormulaHeadFieldOrder.field,h]
  · simp [FormulaHeadFieldOrder.field,h]

def frame (φ : SAT.CNF) : Fin 28 → Tape :=
  FormulaRowGate.frame φ 0 (regTape (FormulaIndexedGraph.labels φ).length)

theorem parked (φ : SAT.CNF) : ∀ t, Parked (frame φ t) :=
  FormulaRowQuery.parked _ _ _ _ _ _ _ _ (parked_regTape _)

theorem merged_hoare (φ : SAT.CNF) (right b : Bool) (ys : List Bool) :
    (placeWorkTM 0 6 (FormulaAllTails.machine right (some b))).HoareTime
      (EmitPred (word φ.encode) (frame φ) ys)
      (EmitPred (word φ.encode) (frame φ) (ys ++ row φ right (.inl b))) (FormulaAllTails.budget φ) := by
  apply FormulaPairExecution.place_hoare _ 0 6 _ _ _ _ _ _ (parked φ) _
    (FormulaAllTails.canonical_hoare φ right (.inl b) ys)
  intro t; fin_cases t <;> rfl

theorem finish_hoare (φ : SAT.CNF) (ys : List Bool) :
    (clearRegTM (9 : Fin 28)).HoareTime
      (EmitPred (word φ.encode) (FormulaRowGate.frame φ (FormulaIndexedGraph.labels φ).length
        (regTape (FormulaIndexedGraph.labels φ).length)) ys)
      (EmitPred (word φ.encode) (frame φ) ys) (2*(FormulaIndexedGraph.labels φ).length+4) := by
  have h := clearRegTM_hoareTime (9 : Fin 28) (FormulaIndexedGraph.labels φ).length (word φ.encode)
    (FormulaRowGate.frame φ (FormulaIndexedGraph.labels φ).length (regTape (FormulaIndexedGraph.labels φ).length)) ys
    (word_parked _) (fun t _ => FormulaRowQuery.parked _ _ _ _ _ _ _ _ (parked_regTape _) t) rfl
  have he : Function.update (FormulaRowGate.frame φ (FormulaIndexedGraph.labels φ).length (regTape (FormulaIndexedGraph.labels φ).length))
      9 (regTape 0) = frame φ := by
    funext t; fin_cases t <;> simp [frame,FormulaRowGate.frame,FormulaRowQuery.frame,FormulaAllTails.frame,
      FormulaExternalTailPhase.frame,FormulaAllRailTails.frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaRailTailReentrant.frame,
      FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he] at h
  exact h

def machine (right : Bool) : TM 28 :=
  seqTM (placeWorkTM 0 6 (FormulaAllTails.machine right (some false)))
    (seqTM (placeWorkTM 0 6 (FormulaAllTails.machine right (some true)))
      (seqTM (FormulaRowLoop.machine right) (clearRegTM 9)))

def budget (φ : SAT.CNF) : Nat := 2*FormulaAllTails.budget φ+
  (FormulaIndexedGraph.labels φ).length*(FormulaRowLoop.bodyBudget φ+2)+3*(FormulaIndexedGraph.labels φ).length+9

theorem canonical_hoare (φ : SAT.CNF) (right : Bool) (ys : List Bool) :
    (machine right).HoareTime (EmitPred (word φ.encode) (frame φ) ys)
      (EmitPred (word φ.encode) (frame φ) (ys ++ bits φ right)) (budget φ) := by
  have h0 := merged_hoare φ right false ys
  have h1 := merged_hoare φ right true (ys ++ row φ right (.inl false))
  have h2 := FormulaRowLoop.hoare φ right (ys ++ row φ right (.inl false) ++ row φ right (.inl true))
  have h3 := finish_hoare φ ((ys ++ row φ right (.inl false) ++ row φ right (.inl true)) ++
    FormulaRowLoop.bits φ right (FormulaIndexedGraph.labels φ).length)
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition (word_parked _)
    (FormulaRowQuery.parked _ _ _ _ _ _ _ _ (parked_regTape _)) _) h3
  have h123 := seqTM_hoareTime _ _ h1 (emitPred_transition (word_parked _) (parked φ) _) h23
  have h := seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) (parked φ) _) h123
  have he := congrArg (fun zs => ys ++ zs) (order φ right)
  simp only [List.append_assoc] at h he
  rw [← he] at h
  exact h.mono_bound (by unfold budget; omega)

end UnconstrainedPACDetection.FormulaRows

module

public import proofs.UnconstrainedPACDetection.FormulaSwitchTailReset

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchTailReentrant
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (tag index)
open FormulaPairExecution (tailMeaning)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)

def frame (i r a L V C : Nat) : Fin 21 → Tape := FormulaSwitchTailHeads.frame i 0 0 r a 0 0 L V L C V

theorem parked (i r a L V C : Nat) : ∀ t, Parked (frame i r a L V C t) :=
  FormulaSwitchTailHeads.frame_parked _ _ _ _ _ _ _ _ _ _ _ _

def machine (p : ControlSwitch.V) (right : Bool) (rt ta : Option Bool) : TM 21 :=
  seqTM (FormulaSwitchTailHeads.machine p right rt ta) FormulaSwitchTailReset.machine

def budget (φ : SAT.CNF) : Nat :=
  FormulaSwitchTailHeads.budget φ (levels φ) 0 0 0 (varCount φ)+6*opBudget (cap φ)+6

theorem hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (ys : List Bool) :
    (machine p right (tag r) (tag a)).HoareTime
      (EmitPred (word φ.encode) (frame i.val (index r) (index a) (levels φ) (varCount φ) φ.length) ys)
      (EmitPred (word φ.encode) (frame i.val (index r) (index a) (levels φ) (varCount φ) φ.length)
        (ys ++ FormulaVertexTailFields.port φ right r a)) (budget φ) := by
  obtain ⟨hL,hV,hC⟩ := FormulaEnumeration.parameter_bounds φ
  have hLc : levels φ+1 ≤ cap φ := by unfold cap; nlinarith
  have hVc : varCount φ ≤ cap φ := by unfold cap; nlinarith
  have hCc : φ.length ≤ cap φ := by unfold cap; nlinarith
  have hB : FormulaClauseCursor.base φ+φ.length ≤ cap φ := by
    have he := congrArg List.length (FormulaClauseCursor.labels φ)
    simp only [List.length_append,FormulaClauseCursor.initialVertices_length,List.length_map,List.length_finRange] at he
    have hn := FormulaIndexedGraph.labels_bound φ
    have hb : FormulaClauseCursor.base φ+φ.length ≤ (FormulaIndexedGraph.labels φ).length := by omega
    apply hb.trans (hn.trans _)
    unfold cap; nlinarith only [Nat.zero_le φ.encode.length]
  have h0 := FormulaSwitchTailCanonical.canonical_hoare φ i p right r a ha 0 0 0 0 (levels φ) (varCount φ) ys
    (Nat.zero_le _) (by exact Nat.le_trans (Nat.le_succ _) hLc)
  have h1 := FormulaSwitchTailReset.hoare i.val (varCount φ) (levels φ+1) (index r) (index a)
    (FormulaClauseCursor.base φ+φ.length) (levels φ+1) (levels φ) (varCount φ) φ.length φ.length (levels φ-1)
    (cap φ) (word φ.encode) (word_parked _) (ys ++ FormulaVertexTailFields.port φ right r a)
    hVc hLc hB hLc hCc (by omega) (by omega) hVc
  have h := seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (FormulaSwitchTailHeads.frame_parked _ _ _ _ _ _ _ _ _ _ _ _) _) h1
  have hi := i.isLt
  exact h.mono_bound (by unfold budget FormulaSwitchTailHeads.budget; omega)

end UnconstrainedPACDetection.FormulaSwitchTailReentrant

module

public import proofs.UnconstrainedPACDetection.FormulaRailTailReset

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailTailReentrant
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaRailHeadPrepare (bank parked)
open VerifierPairRestore (word word_parked)
open FormulaRailHeadVariables (extend extend_parked)
open FormulaVariableTailBound (cap)

def frame (v r L V : Nat) : Fin 18 → Tape := extend (bank 0 v 0 r 0 0 0 L V) (regTape L)

theorem frame_parked (v r L V : Nat) : ∀ t, Parked (frame v r L V t) :=
  extend_parked _ _ (parked _ _ _ _ _ _ _ _ _) (parked_regTape _)

def machine (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 18 :=
  seqTM (FormulaRailTailStaging.machine s) (seqTM (FormulaRailTailBlock.machine s right plan)
    (placeWorkTM 0 1 FormulaRailTailReset.machine))

def budget (φ : SAT.CNF) : Nat := 50*opBudget (cap φ)+FormulaRailTailBlock.budget φ+51

theorem hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine s right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (frame v.val (index r) (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (frame v.val (index r) (levels φ) (varCount φ))
        (ys ++ FormulaRailTailBlock.bits φ v s right r)) (budget φ) := by
  have hL : levels φ ≤ cap φ := by
    have h := (FormulaEnumeration.parameter_bounds φ).1
    unfold cap; nlinarith
  have hv : v.val ≤ cap φ := by
    have h := (FormulaEnumeration.parameter_bounds φ).2.1
    have hv := v.isLt
    unfold cap; nlinarith
  have hN : (FormulaIndexedGraph.labels φ).length ≤ cap φ := by
    apply (FormulaIndexedGraph.labels_bound φ).trans
    unfold cap; nlinarith only [Nat.zero_le φ.encode.length]
  have hA : FormulaRailBase.value (levels φ) (varCount φ) v.val s+levels φ ≤ cap φ := by
    obtain ⟨pre,post,hp,hl⟩ := FormulaRailBase.factor φ v s
    have hi := FormulaRailCursor.port_index φ v s pre post hp (Fin.last (levels φ))
    simp only [hl,Fin.val_last] at hi
    have h := FormulaCoefficientRound.index_bound (FormulaRailCursor.port φ v s (Fin.last (levels φ)))
    rw [hi] at h
    exact h.trans hN
  have hB : 20*levels φ+v.val+1 ≤ cap φ := by
    have h := FormulaCoefficientRound.index_bound (FormulaVariableCursor.port φ v.succ)
    rw [FormulaVariableCursor.port_index] at h
    exact (by simpa [Nat.add_assoc] using h : 20*levels φ+v.val+1 ≤ (FormulaIndexedGraph.labels φ).length).trans hN
  have h0 := FormulaRailTailStaging.hoare φ v s 0 0 (index r) 0 0 0 (levels φ) ys
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) hL
  have h1 := FormulaRailTailBlock.canonical_hoare φ v s right r ys
  have h2 := FormulaRailTailReset.hoare (levels φ) v.val (levels φ) (index r)
    (FormulaRailBase.value (levels φ) (varCount φ) v.val s+levels φ)
    (20*levels φ+v.val+1) v.val (levels φ) (varCount φ) (cap φ) (word φ.encode) (word_parked _)
    (ys ++ FormulaRailTailBlock.bits φ v s right r) hL hL hA hB hv
  have h2' := FormulaRailHeadVariables.lift_hoare _ _ _ _ (regTape (levels φ)) _ _ _
    (parked _ _ _ _ _ _ _ _ _) (parked_regTape _) h2
  have h12 := seqTM_hoareTime _ _ h1
    (emitPred_transition (word_parked _) (extend_parked _ _ (parked _ _ _ _ _ _ _ _ _) (parked_regTape _)) _) h2'
  exact (seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (FormulaRailTailLoop.parked _ _ _ _ _ _ _ (parked_regTape _)) _) h12).mono_bound
      (by unfold budget; omega)

def signs (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 18 :=
  seqTM (machine false right plan) (machine true right plan)

def bits (φ : SAT.CNF) (v : Fin (varCount φ)) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : List Bool :=
  FormulaRailTailBlock.bits φ v false right r ++ FormulaRailTailBlock.bits φ v true right r

theorem signs_hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (signs right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (frame v.val (index r) (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (frame v.val (index r) (levels φ) (varCount φ))
        (ys ++ bits φ v right r)) (2*budget φ+1) := by
  have h0 := hoare φ v false right r ys
  have h1 := hoare φ v true right r (ys ++ FormulaRailTailBlock.bits φ v false right r)
  have h := seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (frame_parked _ _ _ _) _) h1
  rw [List.append_assoc] at h
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.FormulaRailTailReentrant

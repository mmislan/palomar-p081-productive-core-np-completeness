module

public import proofs.UnconstrainedPACDetection.FormulaAllVariableTails

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseTailBody
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open VerifierPairRestore (word word_parked)
open FormulaClauseTailHeads (frame parked)
open FormulaVariableTailBound (cap)

def advance : TM 21 := seqTM (incRegTM 3)
  (seqTM (incRegTM 10) (seqTM (clearRegTM 0) (clearRegTM 11)))

theorem advance_hoare (i c r a b L V C M : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool)
    (hiM : i ≤ M) (hc : c ≤ M) (ha : a ≤ M) (hb : b ≤ M) :
    advance.HoareTime (EmitPred inp (frame i c r a b L V C (regTape L)) ys)
      (EmitPred inp (frame 0 (c+1) r (a+1) 0 L V C (regTape L)) ys) (4*opBudget M+3) := by
  have h0 := (incRegTM_hoareTime (3 : Fin 21) c inp (frame i c r a b L V C (regTape L)) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ (parked_regTape _) t) rfl).mono_bound (incRegTM_le_opBudget hc)
  have he0 : Function.update (frame i c r a b L V C (regTape L)) 3 (regTape (c+1)) =
      frame i (c+1) r a b L V C (regTape L) := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaSwitchVariableHeads.extend,FormulaClauseHeadLoop.bank]
  rw [he0] at h0
  have h1 := (incRegTM_hoareTime (10 : Fin 21) a inp (frame i (c+1) r a b L V C (regTape L)) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ (parked_regTape _) t) rfl).mono_bound (incRegTM_le_opBudget ha)
  have he1 : Function.update (frame i (c+1) r a b L V C (regTape L)) 10 (regTape (a+1)) =
      frame i (c+1) r (a+1) b L V C (regTape L) := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaSwitchVariableHeads.extend,FormulaClauseHeadLoop.bank]
  rw [he1] at h1
  have h2 := (clearRegTM_hoareTime (0 : Fin 21) i inp (frame i (c+1) r (a+1) b L V C (regTape L)) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ (parked_regTape _) t) rfl).mono_bound (clearRegTM_le_opBudget hiM)
  have he2 : Function.update (frame i (c+1) r (a+1) b L V C (regTape L)) 0 (regTape 0) =
      frame 0 (c+1) r (a+1) b L V C (regTape L) := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaSwitchVariableHeads.extend,FormulaClauseHeadLoop.bank]
  rw [he2] at h2
  have h3 := (clearRegTM_hoareTime (11 : Fin 21) b inp (frame 0 (c+1) r (a+1) b L V C (regTape L)) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ (parked_regTape _) t) rfl).mono_bound (clearRegTM_le_opBudget hb)
  have he3 : Function.update (frame 0 (c+1) r (a+1) b L V C (regTape L)) 11 (regTape 0) =
      frame 0 (c+1) r (a+1) 0 L V C (regTape L) := by
    funext t; fin_cases t <;> simp [frame,FormulaChangingFrame.extend,FormulaSwitchVariableHeads.extend,FormulaClauseHeadLoop.bank]
  rw [he3] at h3
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) h3
  have h123 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) h23
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) h123).mono_bound (by omega)

def machine (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 21 :=
  seqTM (FormulaClauseTailPrepare.machine right plan) advance

def budget (φ : SAT.CNF) : Nat :=
  4*opBudget (cap φ)+2*(levels φ)^2+9*levels φ+42+FormulaClauseTailHeads.loopBudget φ

theorem hoare (φ : SAT.CNF) (c : Fin φ.length) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (frame 0 c.val (index r) (FormulaClauseCursor.base φ+c.val) 0
        (levels φ) (varCount φ) φ.length (regTape (levels φ))) ys)
      (EmitPred (word φ.encode) (frame 0 (c.val+1) (index r) (FormulaClauseCursor.base φ+(c.val+1)) 0
        (levels φ) (varCount φ) φ.length (regTape (levels φ)))
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
          (FormulaHeadFieldOrder.field φ right r (FormulaClauseCursor.port φ c)))) (budget φ) := by
  let a := FormulaClauseCursor.port φ c
  have ha : tailMeaning φ a = .inr (.clause c.castSucc) := by
    simp [a,tailMeaning,FormulaClauseCursor.port,tailVertex,MarkedGraph.decode]
    rfl
  have ht : tag a = none := rfl
  have hai : index a = FormulaClauseCursor.base φ+c.val := FormulaClauseCursor.port_index φ c
  have h0 := FormulaClauseTailCanonical.canonical_hoare φ c right r a ha 0 0 (levels φ) ys
  rw [ht,hai] at h0
  obtain ⟨hL,_,hC⟩ := FormulaEnumeration.parameter_bounds φ
  have hc := c.isLt
  have hLc : levels φ ≤ cap φ := by unfold cap; nlinarith
  have hCc : c.val ≤ cap φ := by unfold cap; nlinarith
  have hBc : 20*levels φ+2 ≤ cap φ := by unfold cap; nlinarith
  have hA : FormulaClauseCursor.base φ+c.val ≤ cap φ := by
    have hn := FormulaIndexedGraph.labels_bound φ
    have hi := FormulaCoefficientRound.index_bound a
    rw [hai] at hi
    apply hi.trans (hn.trans _)
    unfold cap; nlinarith only [Nat.zero_le φ.encode.length]
  have h1 := advance_hoare (levels φ) c.val (index r) (FormulaClauseCursor.base φ+c.val)
    (20*levels φ+2) (levels φ) (varCount φ) φ.length (cap φ) (word φ.encode) (word_parked _)
    (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaHeadFieldOrder.field φ right r a)) hLc hCc hA hBc
  have he : FormulaClauseCursor.base φ+c.val+1 = FormulaClauseCursor.base φ+(c.val+1) := by omega
  rw [he] at h1
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _)
    (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) h1).mono_bound (by unfold budget; omega)

end UnconstrainedPACDetection.FormulaClauseTailBody

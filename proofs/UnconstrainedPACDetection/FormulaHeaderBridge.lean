module

public import proofs.UnconstrainedPACDetection.FormulaHeaderStaging

@[expose] public section

namespace UnconstrainedPACDetection.FormulaHeaderBridge
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)

theorem clean_hoare (src ys : List Bool) : (VerifierTapeCleanup.machine (6 : Fin 28)).HoareTime
    (EmitPred (word src) (FormulaHeaderFrame.frame src) ys)
    (EmitPred (word src) (FormulaUnaryScript.frame (FormulaHeaderStaging.initial
      (FormulaHeaders.clauses src) (FormulaHeaderPreparation.occurrences src) (FormulaHeaderPreparation.maximum src+1)
      (FormulaEntityHeader.value src) (FormulaHeaders.value src))) ys)
    (2*(FormulaHeaders.value src).bits.length+9) := by
  have h := FormulaReactionFinish.cleanup_emit (6 : Fin 28) (FormulaHeaders.value src).bits ys
    (word src) (FormulaHeaderFrame.frame src) (word_parked _) (FormulaHeaderFrame.parked src) rfl
  have he : Function.update (FormulaHeaderFrame.frame src) 6 (word []) =
      FormulaUnaryScript.frame (FormulaHeaderStaging.initial (FormulaHeaders.clauses src)
        (FormulaHeaderPreparation.occurrences src) (FormulaHeaderPreparation.maximum src+1)
        (FormulaEntityHeader.value src) (FormulaHeaders.value src)) := by
    funext t
    fin_cases t <;> simp [FormulaHeaderFrame.frame,FormulaHeaderFrame.small,FormulaUnaryScript.frame,
      FormulaHeaderStaging.initial]
    all_goals first | exact FormulaEndpointRegisters.unary_word 0 | exact FormulaEndpointRegisters.unary_word 1
  rw [he] at h
  exact h.mono_bound (by change 1+2*(FormulaHeaders.value src).bits.length+8 ≤ _; omega)

theorem parameters (φ : SAT.CNF) :
    FormulaHeaders.clauses φ.encode=φ.length ∧
    FormulaHeaderPreparation.occurrences φ.encode+1=levels φ ∧
    FormulaHeaderPreparation.maximum φ.encode+1=varCount φ := by
  obtain ⟨hc,hl⟩ := FormulaTokenCount.decoded_counts φ.encode φ (SAT.CNF.decode?_encode φ)
  have hm := FormulaMaximum.decoded_maximum φ.encode φ (SAT.CNF.decode?_encode φ)
  refine ⟨hc,hl,?_⟩
  simpa only [FormulaHeaderPreparation.maximum,FormulaMaximumFrame.value,varCount] using congrArg (fun n => n+1) hm

theorem reaction_label_count (φ : SAT.CNF) :
    FormulaHeaders.value φ.encode+2 = (FormulaIndexedGraph.labels φ).length := by
  obtain ⟨hc,hl,hv⟩ := parameters φ
  rw [FormulaRowBoundary.labels_length]
  unfold FormulaHeaders.value FormulaReactionRegisters.value
  rw [hc,hv]
  unfold FormulaClauseCursor.base FormulaRailBase.value
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
  rw [← hl]
  ring

def machine : TM 28 := seqTM (VerifierTapeCleanup.machine 6) FormulaHeaderStaging.machine

def budget (src : List Bool) : Nat := 2*(FormulaHeaders.value src).bits.length+10+
  27*(opBudget (FormulaHeaderStaging.cap (FormulaHeaders.clauses src) (FormulaHeaderPreparation.occurrences src)
    (FormulaHeaderPreparation.maximum src+1) (FormulaEntityHeader.value src) (FormulaHeaders.value src))+1)

theorem hoare (φ : SAT.CNF) (ys : List Bool) : machine.HoareTime
    (EmitPred (word φ.encode) (FormulaHeaderFrame.frame φ.encode) ys)
    (EmitPred (word φ.encode) (FormulaRows.frame φ) ys) (budget φ.encode) := by
  have h0 := clean_hoare φ.encode ys
  have h1 := FormulaHeaderStaging.hoare (FormulaHeaders.clauses φ.encode) (FormulaHeaderPreparation.occurrences φ.encode)
    (FormulaHeaderPreparation.maximum φ.encode+1) (FormulaEntityHeader.value φ.encode) (FormulaHeaders.value φ.encode)
    (word φ.encode) (word_parked _) ys
  have h := seqTM_hoareTime (VerifierTapeCleanup.machine (6 : Fin 28)) FormulaHeaderStaging.machine
    h0 (emitPred_transition (word_parked _) (fun t => parked_regTape _) _) h1
  obtain ⟨hc,hl,hv⟩ := parameters φ
  have hn := reaction_label_count φ
  have hp : FormulaHeaders.value φ.encode+1=FormulaClauseCursor.base φ+φ.length := by
    rw [FormulaRowBoundary.labels_length] at hn; omega
  have hs : 20*FormulaHeaderPreparation.occurrences φ.encode=20*(levels φ-1) := by omega
  have hw : FormulaRowQuery.frame 0 (FormulaHeaderPreparation.occurrences φ.encode+1)
      (FormulaHeaderPreparation.maximum φ.encode+1) (FormulaHeaders.clauses φ.encode)
      (20*FormulaHeaderPreparation.occurrences φ.encode) (FormulaHeaders.value φ.encode+1)
      (FormulaHeaders.value φ.encode+2) (regTape (FormulaHeaders.value φ.encode+2)) = FormulaRows.frame φ := by
    rw [hc,hl,hv,hp,hn,hs]
    rfl
  rw [hw] at h
  exact h.mono_bound (by unfold budget; omega)

end UnconstrainedPACDetection.FormulaHeaderBridge

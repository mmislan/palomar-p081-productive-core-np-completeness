module

public import proofs.UnconstrainedPACDetection.VerifierCanonicalBuffers

@[expose] public section

namespace UnconstrainedPACDetection.VerifierSizedPhase
open Complexity Complexity.TM
open VerifierCanonicalCoordinates
open VerifierCanonicalContribution (product magnitude)
open VerifierCanonicalLoop (reaction suffix)
open VerifierCanonicalBuffers (running envelope)
open VerifierReactionLoop (frame sourcePred)
open VerifierBufferedProduct (wordTape)

theorem final_budget (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (b : Bool) (x : Fin s.entities)
    (w : BinaryWitnessData.Witness) (hw : w.flow.length = s.reactions) (p₀ n₀ : List Bool) :
    VerifierCanonicalPhase.finalCost s hn b x w
      (running s hn b x w p₀ n₀ (s.reactions-1)).1
      (running s hn b x w p₀ n₀ (s.reactions-1)).2 ≤ 120*(envelope s w p₀ n₀+1)^2 := by
  have h := VerifierCanonicalBuffers.body_budget s hs hn b x w hw p₀ n₀ (s.reactions-1) (by omega)
  have hk := witnessPrefix_length w (s.reactions-1) (by rw [hw]; omega)
  have hr := VerifierCanonicalLoop.reaction_val s hn (s.reactions-1) (by omega)
  refine le_trans ?_ h
  dsimp [VerifierCanonicalPhase.finalCost,VerifierReactionLoop.bodyBound,product]
  rw [hr,hk]
  omega

/-- The full coefficient-side machine, with canonical running totals and an
explicit polynomial bound in encoded source/witness and initial-buffer lengths. -/
theorem sized_phase (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (b : Bool) (x : Fin s.entities)
    (w : BinaryWitnessData.Witness) (hw : w.flow.length = s.reactions) (p₀ n₀ : List Bool) :
    (VerifierCanonicalPhase.machine b).HoareTime
      (fun inp work out => sourcePred (suffix s hn b x 0) inp ∧
        work = frame 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) p₀ n₀ ∧ OutAcc [] out)
      (fun inp work out => sourcePred (sourceSuffix s b (reaction s hn (s.reactions-1)) x) inp ∧
        work = frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode)
          (running s hn b x w p₀ n₀ s.reactions).1
          (running s hn b x w p₀ n₀ s.reactions).2 ∧ OutAcc [] out)
      (250*(envelope s w p₀ n₀+1)^3) := by
  have h := VerifierCanonicalPhase.phase_hoare s hs hn b x w hw
    (fun i => (running s hn b x w p₀ n₀ i).1)
    (fun i => (running s hn b x w p₀ n₀ i).2)
    (120*(envelope s w p₀ n₀+1)^2) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun i hi => VerifierCanonicalBuffers.body_budget s hs hn b x w hw p₀ n₀ i (by omega))
  have hc := VerifierEncodingBounds.reaction_count w
  rw [hw] at hc
  have hv : s.reactions-1 ≤ envelope s w p₀ n₀ := by dsimp [envelope]; omega
  have hl := VerifierReactionBudget.loop_bound (s.reactions-1) (envelope s w p₀ n₀) hv
  have hf := final_budget s hs hn b x w hw p₀ n₀
  have he : (envelope s w p₀ n₀+1)^2 ≤ (envelope s w p₀ n₀+1)^3 := by
    nlinarith
  exact h.mono_bound (by nlinarith)

theorem running_value (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (b : Bool) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (p₀ n₀ : List Bool) (i : ℕ) (hi : i ≤ s.reactions) :
    (BinaryFields.readNat (running s hn b x w p₀ n₀ i).1 : ℤ)-
      BinaryFields.readNat (running s hn b x w p₀ n₀ i).2 =
    (BinaryFields.readNat p₀ : ℤ)-BinaryFields.readNat n₀+
      ∑ j ∈ Finset.range i, (if b then (1 : ℤ) else -1)*
        coefficient s b (reaction s hn j) x*VerifierCanonicalContribution.flow w j := by
  induction i with
  | zero => simp [running,VerifierRunningTotals.totals]
  | succ i ih =>
    have hv := VerifierCanonicalContribution.canonical_value s b (reaction s hn i) x w
      (running s hn b x w p₀ n₀ i).1 (running s hn b x w p₀ n₀ i).2
    rw [VerifierCanonicalLoop.reaction_val s hn i (by omega)] at hv
    change (BinaryFields.readNat (running s hn b x w p₀ n₀ (i+1)).1 : ℤ)-
      BinaryFields.readNat (running s hn b x w p₀ n₀ (i+1)).2 = _ at hv
    rw [hv,ih (by omega),Finset.sum_range_succ]
    ring

end UnconstrainedPACDetection.VerifierSizedPhase

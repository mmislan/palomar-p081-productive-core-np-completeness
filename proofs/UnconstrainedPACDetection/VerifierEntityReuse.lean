module

public import proofs.UnconstrainedPACDetection.VerifierCompareReuse
public import proofs.UnconstrainedPACDetection.VerifierEntityCheck

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntityReuse
open Complexity Complexity.TM
open VerifierEntitySum (bothTotals)
open VerifierCanonicalBuffers (envelope)
open VerifierCanonicalLoop (reaction suffix)
open VerifierCanonicalCoordinates (sourceSuffix)
open VerifierReactionLoop (frame sourcePred)
open VerifierBufferedProduct (wordTape)

def machine : TM 11 := seqTM VerifierEntitySum.machine VerifierCompareReuse.machine

theorem cleared_frame (k stride fuel : ℕ) (wit : Tape) (p q : List Bool) :
    VerifierTapeCleanup.cleared (VerifierTapeCleanup.cleared (frame k stride fuel wit p q) 7) 8 =
      frame k stride fuel wit [] [] := by
  funext j
  fin_cases j <;> simp [VerifierTapeCleanup.cleared,frame,
    VerifierTraversalContribution.extend,VerifierCoefficientIteration.layout,
    VerifierSignedContribution.extend,VerifierWitnessProduct.initial]

theorem budget (N p q : ℕ) (hp : p ≤ 3*N) (hq : q ≤ 3*N) :
    8000*(N+1)^3+1+(3*max p q+2*p+2*q+25) ≤ 8200*(N+1)^3 := by
  have hm : max p q ≤ 3*N := max_le hp hq
  have hN : N+1 ≤ (N+1)^3 := by nlinarith [Nat.zero_le (N^2),Nat.zero_le (N^3)]
  nlinarith only [hp,hq,hm,hN]

theorem entity_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) :
    machine.HoareTime
      (fun inp work out => sourcePred (suffix s hn false x 0) inp ∧
        work = frame 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) [] [] ∧ OutAcc [] out)
      (fun inp work out => sourcePred (sourceSuffix s true (reaction s hn (s.reactions-1)) x) inp ∧
        work = frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode) [] [] ∧
        out.HasBinaryPrefix [VerifierEntityCheck.verdict s hn x w])
      (8200*(envelope s w [] []+1)^3) := by
  let p := (bothTotals s hn x w [] []).1
  let q := (bothTotals s hn x w [] []).2
  let tail := sourceSuffix s true (reaction s hn (s.reactions-1)) x
  let W := frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode) p q
  have hpark := VerifierReactionLoop.frame_parked s.reactions (s.entities-1)
    (s.reactions-1) (wordTape w.encode) p q (VerifierReactionLoop.word_parked w.encode)
  have hsafe : VerifierTapeCleanup.safe W := fun j => ⟨(hpark j).read_ne_start,(hpark j).1⟩
  have hc : VerifierCompareReuse.machine.HoareTime
      (VerifierFlowReset.pred s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode) p q tail)
      (fun inp work out => sourcePred tail inp ∧
        work = frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode) [] [] ∧
        out.HasBinaryPrefix [VerifierEntityCheck.verdict s hn x w])
      (3*max p.length q.length+2*p.length+2*q.length+25) := by
    rintro inp work out ⟨hin,hwork,hout⟩
    have ho : out.HasBinaryPrefix [] :=
      ⟨hout.1,hout.2.2.1,fun i _ => hout.2.2.2 (i+1) (by simp)⟩
    have h := VerifierCompareReuse.reuse_hoare p q W inp out rfl rfl hsafe hin.read_ne_start ho
    obtain ⟨d,t,ht,hd,hh,hi,hw',ho'⟩ := h inp work out ⟨rfl,hwork,rfl⟩
    refine ⟨d,t,ht,hd,hh,hi ▸ hin,?_,ho'⟩
    exact hw'.trans (cleared_frame _ _ _ _ _ _)
  have hsum := VerifierEntitySum.entity_hoare s hs hn x w hw [] []
  have h := seqTM_hoareTime _ _ hsum
    (VerifierFlowReset.stable s.reactions (s.entities-1) (s.reactions-1)
      (wordTape w.encode) p q tail (VerifierReactionLoop.word_parked w.encode)) hc
  have hl := VerifierCanonicalBuffers.buffer_bounds s hs hn false x w hw [] [] s.reactions le_rfl
  have hr := VerifierCanonicalBuffers.buffer_bounds s hs hn true x w hw
    (VerifierEntitySum.leftTotals s hn x w [] []).1
    (VerifierEntitySum.leftTotals s hn x w [] []).2 s.reactions le_rfl
  change (VerifierEntitySum.leftTotals s hn x w [] []).1.length ≤ envelope s w [] [] ∧
    (VerifierEntitySum.leftTotals s hn x w [] []).2.length ≤ envelope s w [] [] at hl
  change p.length ≤ _ ∧ q.length ≤ _ at hr
  have hpq : p.length ≤ 3*envelope s w [] [] ∧ q.length ≤ 3*envelope s w [] [] := by
    dsimp only [envelope,List.length_nil] at hl hr ⊢
    omega
  exact h.mono_bound (budget _ _ _ hpq.1 hpq.2)

end UnconstrainedPACDetection.VerifierEntityReuse

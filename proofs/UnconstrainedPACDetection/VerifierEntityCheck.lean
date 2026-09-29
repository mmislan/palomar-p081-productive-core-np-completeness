module

public import proofs.UnconstrainedPACDetection.VerifierTotalsCompare

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntityCheck
open Complexity Complexity.TM
open VerifierEntitySum (bothTotals)
open VerifierCanonicalBuffers (envelope)
open VerifierCanonicalLoop (reaction suffix)
open VerifierCanonicalCoordinates (sourceSuffix coefficient)
open VerifierReactionLoop (frame sourcePred)
open VerifierBufferedProduct (wordTape)

def machine : TM 11 := seqTM VerifierEntitySum.machine VerifierTotalsCompare.machine

def verdict (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions) (x : Fin s.entities)
    (w : BinaryWitnessData.Witness) :=
  VerifierBinaryCompare.compare false (bothTotals s hn x w [] []).1 (bothTotals s hn x w [] []).2

theorem verdict_iff (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (x : Fin s.entities) (w : BinaryWitnessData.Witness) :
    verdict s hn x w = true ↔ 0 < ∑ j ∈ Finset.range s.reactions,
      ((coefficient s true (reaction s hn j) x : ℤ)-coefficient s false (reaction s hn j) x)*
        VerifierCanonicalContribution.flow w j := by
  have h := VerifierEntitySum.net_value s hn x w [] []
  simp only [BinaryFields.readNat] at h
  rw [verdict,VerifierBinaryCompare.compare_false_iff]
  omega

theorem check_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) :
    machine.HoareTime
      (fun inp work out => sourcePred (suffix s hn false x 0) inp ∧
        work = frame 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) [] [] ∧ OutAcc [] out)
      (fun inp work out => sourcePred (sourceSuffix s true (reaction s hn (s.reactions-1)) x) inp ∧
        (∀ j, j ≠ 7 → j ≠ 8 → work j =
          frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode)
            (bothTotals s hn x w [] []).1 (bothTotals s hn x w [] []).2 j) ∧
        out.HasBinaryPrefix [verdict s hn x w])
      (8000*(envelope s w [] []+1)^3+
        max (bothTotals s hn x w [] []).1.length (bothTotals s hn x w [] []).2.length+2) := by
  let p := (bothTotals s hn x w [] []).1
  let q := (bothTotals s hn x w [] []).2
  let tail := sourceSuffix s true (reaction s hn (s.reactions-1)) x
  have hwp := VerifierReactionLoop.word_parked w.encode
  have hc : VerifierTotalsCompare.machine.HoareTime
      (VerifierFlowReset.pred s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode) p q tail)
      (fun inp work out => sourcePred tail inp ∧
        (∀ j, j ≠ 7 → j ≠ 8 → work j =
          frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode) p q j) ∧
        out.HasBinaryPrefix [VerifierBinaryCompare.compare false p q]) (max p.length q.length+1) := by
    intro inp work out h
    let c : Cfg 11 VerifierTotalsCompare.machine.Q := ⟨VerifierTotalsCompare.machine.qstart,inp,work,out⟩
    have h7 : (c.work 7).HasBinarySuffix p := by
      change (work 7).HasBinarySuffix p
      rw [h.2.1]
      exact (Tape.init_move_right_hasBinaryString p).hasBinarySuffix
    have h8 : (c.work 8).HasBinarySuffix q := by
      change (work 8).HasBinarySuffix q
      rw [h.2.1]
      exact (Tape.init_move_right_hasBinaryString q).hasBinarySuffix
    have hm : (c.work 7).StartInvariant := by
      change (work 7).StartInvariant
      rw [h.2.1]
      exact (Tape.StartInvariant.init_ofBool p).move .right
    have hf : ∀ j, j ≠ 7 → j ≠ 8 → (c.work j).read ≠ .start := by
      intro j _ _
      change (work j).read ≠ .start
      rw [h.2.1]
      exact (VerifierReactionLoop.frame_parked _ _ _ _ _ _ hwp j).read_ne_start
    have ho : c.output.HasBinaryPrefix [] :=
      ⟨h.2.2.1,h.2.2.2.2.1,fun i _ => h.2.2.2.2.2 (i+1) (by simp)⟩
    obtain ⟨d,hr,hh,hout,hin,hwork⟩ := VerifierTotalsCompare.comparison_run p q c rfl h7 hm h8 hf h.1.read_ne_start ho
    refine ⟨d,_,le_rfl,hr,hh,?_,?_,hout⟩
    · rw [hin]; exact h.1
    · intro j h7' h8'
      exact (hwork j h7' h8').trans (congrFun h.2.1 j)
  have hsum := VerifierEntitySum.entity_hoare s hs hn x w hw [] []
  have h := seqTM_hoareTime _ _ hsum
    (VerifierFlowReset.stable s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode) p q tail hwp) hc
  exact h.mono_bound (by dsimp [p,q]; omega)

theorem comparison_budget (N c : ℕ) (hc : c ≤ 3*N) :
    8000*(N+1)^3+c+2 ≤ 8100*(N+1)^3 := by
  have hN : N+1 ≤ (N+1)^3 := by nlinarith [Nat.zero_le (N^2),Nat.zero_le (N^3)]
  nlinarith only [hc,hN]

theorem time_bound (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) :
    8000*(envelope s w [] []+1)^3+
      max (bothTotals s hn x w [] []).1.length (bothTotals s hn x w [] []).2.length+2 ≤
        8100*(envelope s w [] []+1)^3 := by
  have hl := VerifierCanonicalBuffers.buffer_bounds s hs hn false x w hw [] [] s.reactions le_rfl
  have hr := VerifierCanonicalBuffers.buffer_bounds s hs hn true x w hw
    (VerifierEntitySum.leftTotals s hn x w [] []).1
    (VerifierEntitySum.leftTotals s hn x w [] []).2 s.reactions le_rfl
  change (VerifierEntitySum.leftTotals s hn x w [] []).1.length ≤ envelope s w [] [] ∧
    (VerifierEntitySum.leftTotals s hn x w [] []).2.length ≤ envelope s w [] [] at hl
  change (bothTotals s hn x w [] []).1.length ≤ _ ∧
    (bothTotals s hn x w [] []).2.length ≤ _ at hr
  apply comparison_budget
  dsimp only [envelope, List.length_nil] at hl hr ⊢
  omega

theorem sized_check_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) :
    machine.HoareTime
      (fun inp work out => sourcePred (suffix s hn false x 0) inp ∧
        work = frame 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) [] [] ∧ OutAcc [] out)
      (fun inp work out => sourcePred (sourceSuffix s true (reaction s hn (s.reactions-1)) x) inp ∧
        (∀ j, j ≠ 7 → j ≠ 8 → work j =
          frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode)
            (bothTotals s hn x w [] []).1 (bothTotals s hn x w [] []).2 j) ∧
        out.HasBinaryPrefix [verdict s hn x w])
      (8100*(envelope s w [] []+1)^3) := by
  exact (check_hoare s hs hn x w hw).mono_bound (time_bound s hs hn x w hw)

end UnconstrainedPACDetection.VerifierEntityCheck

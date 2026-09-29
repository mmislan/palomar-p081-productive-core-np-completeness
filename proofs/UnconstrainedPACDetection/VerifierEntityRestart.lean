module

public import proofs.UnconstrainedPACDetection.VerifierCursorReset

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntityRestart
open Complexity Complexity.TM
open VerifierCanonicalBuffers (envelope)
open VerifierCanonicalLoop (suffix)
open VerifierReactionLoop (frame sourcePred)
open VerifierBufferedProduct (wordTape)

def machine : TM 11 := seqTM VerifierEntityReuse.machine VerifierCursorReset.restart

theorem budget (N S n t u h : ℕ) (hS : S ≤ N) (hn : n ≤ N)
    (ht : t ≤ 8200*(N+1)^3) (hh : h ≤ S+1+t) (hu : u ≤ h+2*n+15) :
    t+1+u ≤ 17000*(N+1)^3 := by
  have hN : N+1 ≤ (N+1)^3 := by nlinarith [Nat.zero_le (N^2),Nat.zero_le (N^3)]
  nlinarith only [hS,hn,ht,hh,hu,hN]

theorem entity_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) :
    machine.HoareTime
      (fun inp work out => sourcePred (suffix s hn false x 0) inp ∧
        inp.cells = (wordTape s.encode).cells ∧ inp.head ≤ s.encode.length+1 ∧
        work = frame 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) [] [] ∧ OutAcc [] out)
      (VerifierCursorReset.pred [VerifierEntityCheck.verdict s hn x w]
        1 (s.entities-1) (s.reactions-1) (wordTape w.encode) [] [] s.encode)
      (17000*(envelope s w [] []+1)^3) := by
  rintro inp work out ⟨hin,hcells,hhead,hwork,hout⟩
  obtain ⟨d,t,ht,hd,hh,hi,hw',ho⟩ := VerifierEntityReuse.entity_hoare s hs hn x w hw
    inp work out ⟨hin,hwork,hout⟩
  have hc : d.input.cells = (wordTape s.encode).cells :=
    (input_cells_eq_of_reachesIn hd).trans hcells
  have hb := VerifierEntityReuse.machine.input_head_reachesIn_bound hd
  have hbd : d.input.head ≤ s.encode.length+1+t := by exact hb.trans (Nat.add_le_add_right hhead t)
  have hr := VerifierCursorReset.restart_hoare [VerifierEntityCheck.verdict s hn x w] s.encode
    s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode) d.input d.output [] [] hc
    (VerifierReactionLoop.word_parked w.encode) rfl ho
  obtain ⟨e,u,hu,he,heh,hepost⟩ := hr d.input d.work d.output ⟨rfl,hw',rfl⟩
  have hswork : ∀ j, (d.work j).read ≠ .start := by
    intro j
    rw [hw']
    exact (VerifierReactionLoop.frame_parked _ _ _ _ _ _ (VerifierReactionLoop.word_parked w.encode) j).read_ne_start
  have hot : d.output.read ≠ .start := by rw [ho.read_blank]; decide
  have htrans := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start hswork hot
  have he' : VerifierCursorReset.restart.reachesIn u
      ⟨VerifierCursorReset.restart.qstart,transitionInput d.input,
        (fun j => transitionTape (d.work j)),transitionTape d.output⟩ e := by
    simpa only [htrans.1,htrans.2.1,htrans.2.2] using he
  have hseq := seqTM_reachesIn_of_reachesIn _ _ hd hh he'
  refine ⟨phase2Wrap VerifierEntityReuse.machine VerifierCursorReset.restart e,t+1+u,?_,hseq,?_,hepost⟩
  · have hnle := VerifierEncodingBounds.reaction_count w
    rw [hw] at hnle
    apply budget (envelope s w [] []) s.encode.length s.reactions t u d.input.head
    · simp only [envelope,List.length_nil]; omega
    · simp only [envelope,List.length_nil]; omega
    · exact ht
    · exact hbd
    · exact hu
  · change (seqTM VerifierEntityReuse.machine VerifierCursorReset.restart).halted _
    rw [phase2Wrap_halted_iff]; exact heh

end UnconstrainedPACDetection.VerifierEntityRestart

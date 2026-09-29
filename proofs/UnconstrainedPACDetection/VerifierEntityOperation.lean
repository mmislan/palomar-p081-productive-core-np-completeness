module

public import proofs.UnconstrainedPACDetection.VerifierEntityLift

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntityOperation
open Complexity Complexity.TM
open VerifierEntityLift (frame)
open VerifierIndexedField (counter)
open VerifierBufferedProduct (wordTape)
open VerifierReactionLoop (sourcePred)

def machine : TM 13 := seqTM VerifierEntityNavigate.machine VerifierEntityLift.machine

theorem frame_read (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (index : Tape) (hi : index.read ≠ .start) (j : Fin 13) :
    (frame s w index j).read ≠ .start := by
  by_cases hj : j.val < 11
  · simp only [frame,dite_eq_left hj]
    exact (VerifierReactionLoop.frame_parked _ _ _ _ _ _
      (VerifierReactionLoop.word_parked w.encode) _).read_ne_start
  · simp only [frame,dite_eq_right hj]
    split
    · exact (VerifierReactionLoop.word_parked []).read_ne_start
    · exact hi

theorem entity_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (a : Bool) :
    machine.HoareTime
      (fun inp work out => sourcePred s.encode inp ∧ inp.cells = (wordTape s.encode).cells ∧
        work = frame s w (counter (2+x.val)) ∧ out.HasBinaryPrefix [a])
      (fun inp work out => sourcePred s.encode inp ∧ inp.cells = (wordTape s.encode).cells ∧
        work = frame s w (counter (2+x.val)) ∧
        out.HasBinaryPrefix [VerifierEntityCheck.verdict s hn x w && a])
      (17000*(VerifierCanonicalBuffers.envelope s w [] []+1)^3+3*s.encode.length+13) := by
  rintro inp work out ⟨hi,hcells,hwork,hout⟩
  have hc : (counter (2+x.val)).read ≠ .start :=
    (VerifierReactionLoop.word_parked _).read_ne_start
  have ho : out.read ≠ .start := by rw [hout.read_blank]; decide
  obtain ⟨d,t,ht,hd,hh,hin,hdcells,hdhead,hdwork,hdout⟩ :=
    VerifierEntityNavigate.navigate_prepared s hs hn x (frame s w (counter (2+x.val))) out
      rfl (fun j _ => frame_read s w _ hc j) ho (by have := hout.1; simp at this; omega)
      inp work out ⟨hi,hcells,hwork,rfl⟩
  have hdo : d.output.HasBinaryPrefix [a] := hdout ▸ hout
  obtain ⟨e,u,hu,he,heh,hepost⟩ := VerifierEntityLift.entity_hoare s hs hn x w hw _ hc a
    d.input d.work d.output ⟨hin,hdcells,hdhead,hdwork,hdo⟩
  have hfw : ∀ j, (d.work j).read ≠ .start := by
    intro j
    rw [hdwork]
    exact frame_read s w _ hc j
  have htrans := phaseTransition_eq_self_of_reads_ne_start (inp := d.input) (out := d.output)
    hin.read_ne_start hfw (hdout ▸ ho)
  have he' : VerifierEntityLift.machine.reachesIn u
      ⟨VerifierEntityLift.machine.qstart,transitionInput d.input,
        (fun j => transitionTape (d.work j)),transitionTape d.output⟩ e := by
    simpa only [htrans.1,htrans.2.1,htrans.2.2] using he
  have hr := seqTM_reachesIn_of_reachesIn _ _ hd hh he'
  refine ⟨phase2Wrap VerifierEntityNavigate.machine VerifierEntityLift.machine e,
    t+1+u,by omega,hr,?_,hepost⟩
  change (seqTM VerifierEntityNavigate.machine VerifierEntityLift.machine).halted _
  rw [phase2Wrap_halted_iff]
  exact heh

end UnconstrainedPACDetection.VerifierEntityOperation

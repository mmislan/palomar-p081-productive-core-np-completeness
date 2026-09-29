module

public import proofs.UnconstrainedPACDetection.VerifierVerdictCommit

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntityAccumulate
open Complexity Complexity.TM
open VerifierOutputRouting (wrap)
open VerifierReactionLoop (frame sourcePred)
open VerifierBufferedProduct (wordTape)

def machine : TM 12 := seqTM VerifierEntityRestart.machine.retargetOutput VerifierVerdictCommit.machine

theorem entity_run (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (out₀ : Tape) (a : Bool) (ha : out₀.HasBinaryPrefix [a])
    (c : Cfg 11 VerifierEntityRestart.machine.Q) (hq : c.state = VerifierEntityRestart.machine.qstart)
    (hp : sourcePred (VerifierCanonicalLoop.suffix s hn false x 0) c.input ∧
      c.input.cells = (wordTape s.encode).cells ∧ c.input.head ≤ s.encode.length+1 ∧
      c.work = frame 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) [] [] ∧ OutAcc [] c.output) :
    ∃ e t, t ≤ 17000*(VerifierCanonicalBuffers.envelope s w [] []+1)^3+3 ∧
      machine.reachesIn t
        (phase1Wrap VerifierEntityRestart.machine.retargetOutput VerifierVerdictCommit.machine
          (wrap VerifierEntityRestart.machine out₀ c)) e ∧ machine.halted e ∧
      sourcePred s.encode e.input ∧
      (∀ j : Fin 11, e.work j.castSucc = frame 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) [] [] j) ∧
      e.work 11 = wordTape [] ∧
      e.output.HasBinaryPrefix [VerifierEntityCheck.verdict s hn x w && a] ∧
      e.output.cells 0 = out₀.cells 0 := by
  have ho : out₀.read ≠ .start := by rw [ha.read_blank]; decide
  obtain ⟨d,t,ht,hd,hh,hpost,_,hv⟩ := VerifierOutputRouting.entity_run s hs hn x w hw out₀ ho c hq hp
  let D := wrap VerifierEntityRestart.machine out₀ d
  change (D.work 11).HasBinaryPrefix [VerifierEntityCheck.verdict s hn x w] at hv
  have hm : (D.work 11).cells 0 = .start :=
    work_cells_zero_eq_start_of_reachesIn 11 hd (by
      change c.output.cells 0 = .start
      exact hp.2.2.2.2.2.1)
  have hf : ∀ j : Fin 12, j ≠ 11 → (D.work j).read ≠ .start := by
    intro j hj
    have hjlt : j.val < 11 := by
      by_contra h
      have he : j = 11 := Fin.ext (by have := j.isLt; omega)
      exact hj he
    change ((VerifierEntityRestart.machine.retargetCfg d).work j).read ≠ .start
    rw [retargetCfg_work_lt _ _ j hjlt,hpost.2.1]
    exact (VerifierReactionLoop.frame_parked _ _ _ _ _ _ (VerifierReactionLoop.word_parked w.encode) _).read_ne_start
  have hc := VerifierVerdictCommit.commit_hoare (VerifierEntityCheck.verdict s hn x w) a
    D.work D.input D.output hv ha hm hf hpost.1.read_ne_start
  obtain ⟨e,u,hu,he,heh,hei,hew,heo,hem⟩ := hc D.input D.work D.output ⟨rfl,rfl,rfl⟩
  have hall : ∀ j, (D.work j).read ≠ .start := by
    intro j
    by_cases hj : j = 11
    · subst j; rw [hv.read_blank]; decide
    · exact hf j hj
  have htrans := phaseTransition_eq_self_of_reads_ne_start (inp := D.input) (out := D.output)
    hpost.1.read_ne_start hall ho
  have he' : VerifierVerdictCommit.machine.reachesIn u
      ⟨VerifierVerdictCommit.machine.qstart,transitionInput D.input,
        (fun j => transitionTape (D.work j)),transitionTape D.output⟩ e := by
    simpa only [htrans.1,htrans.2.1,htrans.2.2] using he
  have hr := seqTM_reachesIn_of_reachesIn _ _ hd hh he'
  refine ⟨phase2Wrap VerifierEntityRestart.machine.retargetOutput VerifierVerdictCommit.machine e,
    t+1+u,by omega,hr,?_,?_,?_,?_,heo,hem⟩
  · change (seqTM VerifierEntityRestart.machine.retargetOutput VerifierVerdictCommit.machine).halted _
    rw [phase2Wrap_halted_iff]; exact heh
  · change sourcePred s.encode e.input
    rw [hei]; exact hpost.1
  · intro j
    change e.work j.castSucc = _
    rw [hew,Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp at this; omega)]
    change (VerifierEntityRestart.machine.retargetCfg d).work j.castSucc = _
    rw [retargetCfg_work_lt _ _ _ j.isLt,hpost.2.1]
    rfl
  · change e.work 11 = _
    rw [hew,Function.update_self]

end UnconstrainedPACDetection.VerifierEntityAccumulate

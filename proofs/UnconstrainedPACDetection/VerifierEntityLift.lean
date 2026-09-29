module

public import proofs.UnconstrainedPACDetection.VerifierEntityNavigate

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntityLift
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierReactionLoop (sourcePred)

def frame (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (index : Tape) : Fin 13 → Tape := fun j =>
  if h : j.val < 11 then
    VerifierReactionLoop.frame 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) [] [] ⟨j.val,h⟩
  else if j.val = 11 then wordTape [] else index

def machine : TM 13 := placeWorkTM 0 1 VerifierEntityAccumulate.machine

theorem entity_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (index : Tape) (hindex : index.read ≠ .start)
    (a : Bool) :
    machine.HoareTime
      (fun inp work out => sourcePred (VerifierCanonicalLoop.suffix s hn false x 0) inp ∧
        inp.cells = (wordTape s.encode).cells ∧ inp.head ≤ s.encode.length+1 ∧
        work = frame s w index ∧ out.HasBinaryPrefix [a])
      (fun inp work out => sourcePred s.encode inp ∧
        inp.cells = (wordTape s.encode).cells ∧ work = frame s w index ∧
        out.HasBinaryPrefix [VerifierEntityCheck.verdict s hn x w && a])
      (17000*(VerifierCanonicalBuffers.envelope s w [] []+1)^3+3) := by
  rintro inp work out ⟨hi,hcells,hhead,hwork,hout⟩
  subst work
  let c : Cfg 11 VerifierEntityRestart.machine.Q :=
    ⟨VerifierEntityRestart.machine.qstart,inp,
      VerifierReactionLoop.frame 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) [] [],wordTape []⟩
  obtain ⟨d,t,ht,hd,hh,hin,hdw,hds,hdo,_⟩ :=
    VerifierEntityAccumulate.entity_run s hs hn x w hw out a hout c rfl
      ⟨hi,hcells,hhead,rfl,outAcc_nil_init⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierEntityAccumulate.machine 0 1 (frame s w index) hd (by
      intro j hj
      have hjv : j.val = 12 := by
        simp only [placeWorkInMiddle] at hj
        have := j.isLt
        omega
      simpa [frame,hjv] using hindex)
  have he : placeWorkCfg VerifierEntityAccumulate.machine 0 1 (frame s w index)
      (phase1Wrap VerifierEntityRestart.machine.retargetOutput VerifierVerdictCommit.machine
        (VerifierOutputRouting.wrap VerifierEntityRestart.machine out c)) =
      (⟨machine.qstart,inp,frame s w index,out⟩ : Cfg 13 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> rfl
    · rfl
  have hwfinal : (placeWorkCfg VerifierEntityAccumulate.machine 0 1 (frame s w index) d).work =
      frame s w index := by
    funext j
    fin_cases j
    all_goals first
      | exact hdw ⟨0,by decide⟩
      | exact hdw ⟨1,by decide⟩
      | exact hdw ⟨2,by decide⟩
      | exact hdw ⟨3,by decide⟩
      | exact hdw ⟨4,by decide⟩
      | exact hdw ⟨5,by decide⟩
      | exact hdw ⟨6,by decide⟩
      | exact hdw ⟨7,by decide⟩
      | exact hdw ⟨8,by decide⟩
      | exact hdw ⟨9,by decide⟩
      | exact hdw ⟨10,by decide⟩
      | exact hds
      | rfl
  refine ⟨placeWorkCfg VerifierEntityAccumulate.machine 0 1 (frame s w index) d,
    t,ht,?_,hh,hin,?_,hwfinal,hdo⟩
  · change machine.reachesIn _ _ _ at hp
    simpa only [he] using hp
  · exact (input_cells_eq_of_reachesIn hd).trans hcells

end UnconstrainedPACDetection.VerifierEntityLift

module

public import proofs.UnconstrainedPACDetection.VerifierActivationOutput

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationBody
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (empty)

def frame (wt fuel : Tape) : Fin 3 → Tape := fun j =>
  if h : j.val < 2 then VerifierActivationOutput.pair wt (empty .start) ⟨j.val,h⟩ else fuel

def pred (suffix : List Bool) (wt fuel : Tape) (emitted : List Bool) : Complexity.TM.TapePred 3 :=
  fun inp work out => inp.HasBinarySuffix suffix ∧ work = frame wt fuel ∧ OutAcc emitted out

def machine : TM 3 := placeWorkTM 0 1 VerifierActivationOutput.machine

theorem row_hoare (es : List (List Bool × Bool)) (srcTail witTail emitted : List Bool)
    (fuel : Tape) (hf : fuel.read ≠ .start) :
    machine.HoareTime
      (pred (BinaryFields.encode (es.map Prod.fst) ++ srcTail)
        (wordTape (BinaryFields.encodeField (es.map Prod.snd) ++ witTail)) fuel emitted)
      (pred srcTail (wordTape (BinaryFields.encodeField (es.map Prod.snd) ++ witTail)) fuel
        (emitted ++ [VerifierActivationSide.hit es false]))
      ((BinaryFields.encode (es.map Prod.fst)).length+4*es.length+10) := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst work
  let wt := wordTape (BinaryFields.encodeField (es.map Prod.snd) ++ witTail)
  have hop := VerifierEntityLoopBody.prefix_of_acc emitted out hout
  obtain ⟨d,t,ht,hd,hh,hdi,_,_,hdw,hdo⟩ :=
    VerifierActivationOutput.row_output_hoare es srcTail witTail inp out hin
      (by rw [hop.read_blank]; decide) _ _ _ ⟨rfl,rfl,rfl⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierActivationOutput.machine 0 1 (frame wt fuel) hd (by
      intro j hj
      have hjv : j.val = 2 := by
        simp only [placeWorkInMiddle] at hj
        have := j.isLt
        omega
      simpa [frame,hjv] using hf)
  have he : placeWorkCfg VerifierActivationOutput.machine 0 1 (frame wt fuel)
      ⟨VerifierActivationOutput.machine.qstart,inp,VerifierActivationOutput.pair wt (empty .start),out⟩ =
      (⟨machine.qstart,inp,frame wt fuel,out⟩ : Cfg 3 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  refine ⟨placeWorkCfg VerifierActivationOutput.machine 0 1 (frame wt fuel) d,t,ht,?_,hh,hdi,?_,?_⟩
  · change machine.reachesIn _ _ _ at hp
    dsimp only [wt] at he hp
    simpa only [he] using hp
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,frame,hdw]
  · have hmarker : d.output.cells 0 = .start := output_cells_zero_eq_start_of_reachesIn hd hout.2.1
    apply VerifierEntityLoopBody.acc_of_prefix _ d.output _ hmarker
    rw [hdo]
    exact Tape.hasBinaryPrefix_write_bit _ hop

theorem frame_parked (bits : List Bool) (fuel : Tape) (hf : Parked fuel) :
    ∀ j, Parked (frame (wordTape bits) fuel j) := by
  intro j
  fin_cases j
  · exact VerifierReactionLoop.word_parked _
  · change Parked (empty .start)
    rw [VerifierVerdictCommit.empty_start]
    exact VerifierReactionLoop.word_parked _
  · exact hf

theorem update_fuel (wt fuel next : Tape) :
    Function.update (frame wt fuel) 2 next = frame wt next := by
  funext j; fin_cases j <;> simp [frame]

end UnconstrainedPACDetection.VerifierActivationBody

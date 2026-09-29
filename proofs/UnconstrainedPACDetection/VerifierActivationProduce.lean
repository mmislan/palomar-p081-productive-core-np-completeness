module

public import proofs.UnconstrainedPACDetection.VerifierFlowRouting

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationProduce
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierFlowPassHoare (ended)

@[reducible] def frame (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (flags : Tape) : Fin 4 → Tape :=
  fun j => if h : j.val < 3 then VerifierActivationBody.frame (wordTape w.encode)
    (regTape (2*s.reactions)) ⟨j.val,h⟩ else flags

theorem frame_parked (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (flags : Tape) (hf : Parked flags) : ∀ j, Parked (frame s w flags j) := by
  intro j
  by_cases hj : j.val < 3
  · simp only [frame,dite_eq_left hj]
    exact VerifierActivationBody.frame_parked _ _ (parked_regTape _) _
  · simpa only [frame,dite_eq_right hj] using hf

theorem ended_acc (bits : List Bool) : OutAcc bits (ended bits) :=
  VerifierEntityLoopBody.acc_of_prefix bits _
    ⟨rfl,(Tape.init_move_right_hasBinaryString bits).2⟩ rfl

@[reducible] def machine : TM 4 := VerifierActivationLoop.machine.retargetOutput

theorem produce_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (w : BinaryWitnessData.Witness) (hm : w.mask.length = s.entities) (hw : w.flow.length = s.reactions) :
    machine.HoareTime
      (fun inp work out => inp.HasBinarySuffix (BinaryFields.encode (s.values.map Nat.bits)) ∧
        work = frame s w (wordTape []) ∧ out = wordTape [])
      (fun inp work out => inp.HasBinarySuffix [] ∧
        work = frame s w (ended (VerifierActivationSource.flags s w)) ∧ out = wordTape [])
      (20*(s.encode.length+2*w.encode.length+1)^2) := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst work; subst out
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := VerifierActivationSource.wire_hoare s hs w hm hw []
    inp (VerifierActivationBody.frame (wordTape w.encode) (regTape (2*s.reactions))) (wordTape [])
    ⟨hin,rfl,outAcc_nil_init⟩
  have he : d.output = ended (VerifierActivationSource.flags s w) := hdo.eq (ended_acc _)
  have hr := VerifierOutputRouting.run_frame _ (wordTape [])
    (Tape.init_move_right_hasBinaryString _).hasBinarySuffix.read_ne_start hd
  refine ⟨VerifierOutputRouting.wrap _ (wordTape []) d,t,ht,?_,hh,hdi,?_,rfl⟩
  · change VerifierActivationLoop.machine.retargetOutput.reachesIn t _ _
    have hc :
        (⟨machine.qstart,inp,frame s w (wordTape []),wordTape []⟩ : Cfg 4 machine.Q) =
        VerifierOutputRouting.wrap VerifierActivationLoop.machine (wordTape [])
          ⟨VerifierActivationLoop.machine.qstart,inp,
            VerifierActivationBody.frame (wordTape w.encode) (regTape (2*s.reactions)),
            wordTape []⟩ := by
      apply Cfg.ext
      · rfl
      · rfl
      · funext j
        fin_cases j <;> rfl
      · rfl
    rw [hc]
    exact hr
  · funext j
    fin_cases j <;> simp [VerifierOutputRouting.wrap,retargetCfg,frame,hdw,he]

@[reducible] def rewind : TM 4 := placeWorkTM 3 0 (rewindWorkTM (0 : Fin 1))

theorem rewind_hoare (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (inp₀ : Tape) (hi : inp₀.read ≠ .start) :
    rewind.HoareTime
      (VerifierTapeCleanup.frame (frame s w (ended (VerifierActivationSource.flags s w))) inp₀ (wordTape []))
      (VerifierTapeCleanup.frame (frame s w (wordTape (VerifierActivationSource.flags s w))) inp₀ (wordTape []))
      ((VerifierActivationSource.flags s w).length+3) := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst inp; subst work; subst out
  let bits := VerifierActivationSource.flags s w
  let base := frame s w (ended bits)
  have hf : ∀ j, (base j).read ≠ .start := fun j =>
    (frame_parked s w (ended bits)
      ⟨by change 1 ≤ bits.length+1; omega,((Tape.StartInvariant.init_ofBool bits).move .right).2⟩ j).read_ne_start
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := VerifierActivationRow.rewind_hoare bits bits.length inp₀ (wordTape []) hi
    (Tape.init_move_right_hasBinaryString _).hasBinarySuffix.read_ne_start (by change 1 ≤ 1; decide)
    _ _ _ ⟨rfl,rfl,rfl⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal (rewindWorkTM (0 : Fin 1)) 3 0 base hd
    (by intro j _; exact hf j)
  refine ⟨placeWorkCfg (rewindWorkTM (0 : Fin 1)) 3 0 base d,t,ht,?_,hh,hdi,?_,hdo⟩
  · convert hp using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,base,frame,hdw,bits]

end UnconstrainedPACDetection.VerifierActivationProduce

module

public import proofs.UnconstrainedPACDetection.VerifierMaskedEntity

@[expose] public section

/-! The complete entity body with a separately framed outer-fuel tape. -/
namespace UnconstrainedPACDetection.VerifierEntityLoopBody
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierIndexedField (counter)

def frame (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (k : ℕ) (fuel : Tape) : Fin 14 → Tape := fun j =>
  if h : j.val < 13 then VerifierEntityLift.frame s w (counter k) ⟨j.val,h⟩ else fuel

def sourcePred (s : BinarySourceData.DenseSource) (inp : Tape) : Prop :=
  inp.HasBinarySuffix s.encode ∧ inp.cells = (wordTape s.encode).cells

theorem prefix_of_acc (bits : List Bool) (out : Tape) (h : OutAcc bits out) :
    out.HasBinaryPrefix bits :=
  ⟨h.1,h.2.2.1,fun i hi => h.2.2.2 (i+1) (by omega)⟩

theorem acc_of_prefix (bits : List Bool) (out : Tape)
    (h : out.HasBinaryPrefix bits) (hm : out.cells 0 = .start) : OutAcc bits out := by
  refine ⟨h.1,hm,h.2.1,?_⟩
  intro j hj
  have he : j-1+1 = j := by omega
  simpa only [he] using h.2.2 (j-1) (by omega)

def pred (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (k : ℕ) (fuel : Tape) (a : Bool) : Complexity.TM.TapePred 14 :=
  fun inp work out => sourcePred s inp ∧ work = frame s w k fuel ∧ OutAcc [a] out

def machine : TM 14 := placeWorkTM 0 1 VerifierMaskedEntity.machine

theorem entity_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (hm : w.mask.length = s.entities)
    (fuel : Tape) (hf : fuel.read ≠ .start) (a : Bool) :
    machine.HoareTime (pred s w (2+x.val) fuel a)
      (pred s w (2+x.val+1) fuel
        (if w.mask.getD x.val false then VerifierEntityCheck.verdict s hn x w && a else a))
      (VerifierMaskedEntity.bodyBound s w x.val+5*x.val+19) := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst work
  obtain ⟨d,t,ht,hd,hh,hdi,hdc,hdw,hdo⟩ :=
    VerifierMaskedEntity.entity_hoare s hs hn x w hw hm a
      inp (VerifierEntityLift.frame s w (counter (2+x.val))) out
      ⟨hin.1,hin.2,rfl,prefix_of_acc [a] out hout⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierMaskedEntity.machine 0 1 (frame s w (2+x.val) fuel) hd (by
      intro j hj
      have hjv : j.val = 13 := by
        simp only [placeWorkInMiddle] at hj
        have := j.isLt
        omega
      simpa [frame,hjv] using hf)
  have he : placeWorkCfg VerifierMaskedEntity.machine 0 1 (frame s w (2+x.val) fuel)
      ⟨VerifierMaskedEntity.machine.qstart,inp,VerifierEntityLift.frame s w (counter (2+x.val)),out⟩ =
      (⟨machine.qstart,inp,frame s w (2+x.val) fuel,out⟩ : Cfg 14 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  refine ⟨placeWorkCfg VerifierMaskedEntity.machine 0 1 (frame s w (2+x.val) fuel) d,
    t,ht,?_,hh,⟨hdi,hdc⟩,?_,?_⟩
  · change machine.reachesIn _ _ _ at hp
    simpa only [he] using hp
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,frame,hdw]
  · have hmarker : d.output.cells 0 = .start := output_cells_zero_eq_start_of_reachesIn hd hout.2.1
    exact acc_of_prefix _ d.output hdo hmarker

theorem frame_parked (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (k : ℕ) (fuel : Tape) (hf : Parked fuel) : ∀ j, Parked (frame s w k fuel j) := by
  intro j
  by_cases hj : j.val < 13
  · simp only [frame,dite_eq_left hj]
    by_cases hk : j.val < 11
    · simp only [VerifierEntityLift.frame,dite_eq_left hk]
      exact VerifierReactionLoop.frame_parked _ _ _ _ _ _ (VerifierReactionLoop.word_parked _) _
    · simp only [VerifierEntityLift.frame,dite_eq_right hk]
      split <;> exact VerifierReactionLoop.word_parked _
  · simpa only [frame,dite_eq_right hj] using hf

theorem update_fuel (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (k : ℕ) (fuel next : Tape) : Function.update (frame s w k fuel) 13 next = frame s w k next := by
  funext j
  fin_cases j <;> simp [frame]

end UnconstrainedPACDetection.VerifierEntityLoopBody

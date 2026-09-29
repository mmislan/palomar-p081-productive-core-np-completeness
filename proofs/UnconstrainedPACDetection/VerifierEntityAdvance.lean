module

public import proofs.UnconstrainedPACDetection.VerifierEntityOperation

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntityAdvance
open Complexity Complexity.TM
open VerifierEntityLift (frame)
open VerifierIndexedField (counter)

def machine : TM 13 := placeWorkTM 4 0 (VerifierIndexAdvance.machine 8)

theorem successor_hoare (k : ℕ) (w : Fin 13 → Tape) (inp₀ out₀ : Tape)
    (hx : w 12 = counter k) (hw : VerifierTapeCleanup.safe w)
    (hi : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    machine.HoareTime (VerifierTapeCleanup.frame w inp₀ out₀)
      (VerifierTapeCleanup.frame (Function.update w 12 (counter (k+1))) inp₀ out₀) (2*k+6) := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst inp
  subst work
  subst out
  let middle : Fin 9 → Tape := fun j => w ⟨4+j.val,by omega⟩
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := VerifierIndexAdvance.successor_hoare
    8 k middle inp₀ out₀ hx (fun j => hw ⟨4+j.val,by omega⟩) hi ho hoh
    inp₀ middle out₀ ⟨rfl,rfl,rfl⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    (VerifierIndexAdvance.machine 8) 4 0 w hd (fun j _ => (hw j).1)
  have he : placeWorkCfg (VerifierIndexAdvance.machine 8) 4 0 w
      ⟨(VerifierIndexAdvance.machine 8).qstart,inp₀,middle,out₀⟩ =
      (⟨machine.qstart,inp₀,w,out₀⟩ : Cfg 13 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  refine ⟨placeWorkCfg (VerifierIndexAdvance.machine 8) 4 0 w d,t,ht,?_,hh,hdi,?_,hdo⟩
  · change machine.reachesIn _ _ _ at hp
    simpa only [he] using hp
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,hdw,middle]

theorem frame_safe (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (k : ℕ) :
    VerifierTapeCleanup.safe (frame s w (counter k)) := by
  intro j
  refine ⟨VerifierEntityOperation.frame_read s w _
    (VerifierReactionLoop.word_parked _).read_ne_start j,?_⟩
  by_cases hj : j.val < 11
  · simp only [frame,dite_eq_left hj]
    exact (VerifierReactionLoop.frame_parked _ _ _ _ _ _
      (VerifierReactionLoop.word_parked w.encode) _).1
  · simp only [frame,dite_eq_right hj]
    split <;> exact le_rfl

theorem update_frame (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (k l : ℕ) : Function.update (frame s w (counter k)) 12 (counter l) = frame s w (counter l) := by
  funext j
  fin_cases j <;> simp [frame]

theorem advance_hoare (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (k : ℕ) (a : Bool) :
    machine.HoareTime
      (fun inp work out => inp.HasBinarySuffix s.encode ∧
        inp.cells = (VerifierBufferedProduct.wordTape s.encode).cells ∧
        work = frame s w (counter k) ∧ out.HasBinaryPrefix [a])
      (fun inp work out => inp.HasBinarySuffix s.encode ∧
        inp.cells = (VerifierBufferedProduct.wordTape s.encode).cells ∧
        work = frame s w (counter (k+1)) ∧ out.HasBinaryPrefix [a]) (2*k+6) := by
  rintro inp work out ⟨hi,hcells,hwork,hout⟩
  have ho : out.read ≠ .start := by rw [hout.read_blank]; decide
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := successor_hoare k (frame s w (counter k)) inp out
    rfl (frame_safe s w k) hi.read_ne_start ho (by have := hout.1; simp at this; omega)
    inp work out ⟨rfl,hwork,rfl⟩
  refine ⟨d,t,ht,hd,hh,?_,?_,?_,?_⟩
  · rw [hdi]; exact hi
  · rw [hdi]; exact hcells
  · rw [hdw,update_frame]
  · rw [hdo]; exact hout

end UnconstrainedPACDetection.VerifierEntityAdvance

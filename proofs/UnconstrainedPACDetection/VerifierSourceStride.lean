module

public import proofs.UnconstrainedPACDetection.VerifierIndexedField

@[expose] public section

/-! A reusable source-field stride with a persistent counter on physical tape9. -/
namespace UnconstrainedPACDetection.VerifierSourceStride
open Complexity
open Complexity.TM
open VerifierIndexedField (counter exhausted exhausted_off)

def pred (tape : Tape) (suffix : List Bool) (out₀ : Tape) : Tape → (Fin 1 → Tape) → Tape → Prop :=
  fun inp work out => inp.HasBinarySuffix suffix ∧ work = (fun _ => tape) ∧ out = out₀

theorem skip_hoare (fields : List (List Bool)) (suffix : List Bool) (out₀ : Tape)
    (ho : out₀.read ≠ .start) :
    VerifierFieldSkip.machine.HoareTime
      (pred (counter fields.length) (BinaryFields.encode fields ++ suffix) out₀)
      (pred (exhausted fields.length) suffix out₀)
      ((BinaryFields.encode fields).length+fields.length+1) := by
  rintro inp work out ⟨hi,rfl,rfl⟩
  let c : Cfg 1 (Fin 4) := ⟨0,inp,fun _ => counter fields.length,out⟩
  obtain ⟨d,hd,hh,hin,hws,hih,hwh,hic,hwc,hout⟩ := VerifierFieldSkip.skip_run fields suffix c rfl hi
    (Tape.init_move_right_hasBinaryString _).hasBinarySuffix ho
  refine ⟨d,_,le_rfl,hd,hh,hin,?_,hout⟩
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  apply Tape.ext
  · change (d.work 0).head = fields.length+1
    change (d.work 0).head = 1+fields.length at hwh
    omega
  · exact hwc

theorem rewind_hoare (k : ℕ) (suffix : List Bool) (out₀ : Tape)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (rewindWorkTM (0 : Fin 1)).HoareTime (pred (exhausted k) suffix out₀)
      (pred (counter k) suffix out₀) (k+3) := by
  let P : Tape → (Fin 1 → Tape) → Tape → Prop := fun inp work out =>
    inp.HasBinarySuffix suffix ∧ (work 0).cells = (counter k).cells ∧ out = out₀
  have h := rewindWorkTM_hoareTime_frame (0 : Fin 1) (k+1) (P := P) (by
    rintro inp work out inp' work' out' ⟨hi,hc,ho'⟩ hc' _ _ hin hoc hoh'
    exact ⟨hin ▸ hi,hc'.trans hc,(Tape.ext hoh' hoc).trans ho'⟩)
  rintro inp work out ⟨hi,rfl,rfl⟩
  have hm := (Tape.StartInvariant.init_ofBool (List.replicate k true)).move .right
  obtain ⟨d,t,hb,hd,hh,hhead,hin,hcells,hout⟩ := h inp (fun _ => exhausted k) out
    ⟨hm.1,hm.2,le_rfl,hi.read_ne_start,ho,hoh,(by
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))),hi,rfl,rfl⟩
  refine ⟨d,t,by omega,hd,hh,hin,?_,hout⟩
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact Tape.ext hhead hcells

def small : TM 1 := seqTM VerifierFieldSkip.machine (rewindWorkTM 0)

theorem small_hoare (fields : List (List Bool)) (suffix : List Bool) (out₀ : Tape)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    small.HoareTime (pred (counter fields.length) (BinaryFields.encode fields ++ suffix) out₀)
      (pred (counter fields.length) suffix out₀)
      ((BinaryFields.encode fields).length+2*fields.length+5) := by
  have stable : ∀ inp work out, pred (exhausted fields.length) suffix out₀ inp work out →
      pred (exhausted fields.length) suffix out₀ (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
    rintro inp work out ⟨hi,rfl,rfl⟩
    obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start
      (fun _ => exhausted_off fields.length) ho
    exact ⟨by simpa only [hin] using hi,hw,hout⟩
  have h := seqTM_hoareTime _ _ (skip_hoare fields suffix out₀ ho) stable (rewind_hoare fields.length suffix out₀ ho hoh)
  exact h.mono_bound (by omega)

def machine : TM 11 := placeWorkTM 9 1 small

/-- The stride counter is reusable and all arithmetic/loop tapes are exact frames. -/
theorem stride_hoare (fields : List (List Bool)) (suffix : List Bool) (frame : Fin 11 → Tape) (out₀ : Tape)
    (hc : frame 9 = counter fields.length)
    (hf : ∀ j, j ≠ 9 → (frame j).read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    machine.HoareTime
      (fun inp work out => inp.HasBinarySuffix (BinaryFields.encode fields ++ suffix) ∧ work = frame ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix suffix ∧ work = frame ∧ out = out₀)
      ((BinaryFields.encode fields).length+2*fields.length+5) := by
  rintro inp work out ⟨hi,hw,ho'⟩
  subst work
  subst out
  obtain ⟨d,t,hb,hd,hh,hin,hdw,hout⟩ := small_hoare fields suffix out₀ ho hoh
    inp (fun _ => counter fields.length) out₀ ⟨hi,rfl,rfl⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal small 9 1 frame hd (by
    intro j hj
    apply hf j
    intro he
    subst j
    simp [placeWorkInMiddle] at hj)
  have he : placeWorkCfg small 9 1 frame ⟨small.qstart,inp,fun _ => counter fields.length,out₀⟩ =
      (⟨machine.qstart,inp,frame,out₀⟩ : Cfg 11 machine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,hc]
    · rfl
  refine ⟨placeWorkCfg small 9 1 frame d,t,hb,?_,hh,hin,?_,hout⟩
  · change machine.reachesIn _ _ _ at hp
    simpa only [he] using hp
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,hdw,hc]

end UnconstrainedPACDetection.VerifierSourceStride

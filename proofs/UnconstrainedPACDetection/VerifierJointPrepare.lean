module

public import proofs.UnconstrainedPACDetection.VerifierJointWitness
public import proofs.UnconstrainedPACDetection.VerifierSourceHeaders

@[expose] public section

namespace UnconstrainedPACDetection.VerifierJointPrepare
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierJointWitness (layout)

def sourceMachine : TM 11 := placeWorkTM 0 8 VerifierSourceHeaders.readyMachine

def before (src wit : List Bool) : Complexity.TM.TapePred 11 := fun inp work out =>
  inp = wordTape src ∧ work = layout (fun _ => wordTape []) (fun _ => wordTape [])
    (wordTape wit) (wordTape []) ∧ out = wordTape []

def middle (src wit : List Bool) : Complexity.TM.TapePred 11 := fun inp work out =>
  ∃ source prior, VerifierSourceHeaders.framedReady src inp source (one .start prior) ∧
    work = layout source (fun _ => wordTape []) (wordTape wit) (wordTape []) ∧
    out = one .start prior

def after (src wit : List Bool) : Complexity.TM.TapePred 11 := fun inp work out =>
  ∃ source prior, VerifierSourceHeaders.framedReady src inp source (one .start prior) ∧
    VerifierJointWitness.result wit source inp prior true inp work out

theorem source_hoare (src wit : List Bool) : sourceMachine.HoareTime
    (before src wit) (middle src wit) (10*src.length+51) := by
  rintro inp work out ⟨hi,hw,ho⟩
  subst inp; subst work; subst out
  obtain ⟨d,t,ht,hr,hh,hready,hpi,hpw⟩ := VerifierSourceHeaders.ready_framed_hoare src
    (wordTape src) (fun _ => wordTape []) (wordTape []) ⟨rfl,rfl,rfl⟩
  obtain ⟨b,hout,hsem,haccepted⟩ := hready
  let base := layout (fun _ => wordTape []) (fun _ => wordTape []) (wordTape wit) (wordTape [])
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierSourceHeaders.readyMachine 0 8 base hr (by
      intro j hj; fin_cases j
      all_goals try (simp [placeWorkInMiddle] at hj)
      all_goals exact (VerifierReactionLoop.word_parked _).read_ne_start)
  have he : placeWorkCfg VerifierSourceHeaders.readyMachine 0 8 base
      ⟨VerifierSourceHeaders.readyMachine.qstart,wordTape src,fun _ => wordTape [],wordTape []⟩ =
      (⟨sourceMachine.qstart,wordTape src,base,wordTape []⟩ : Cfg 11 sourceMachine.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  rw [he] at hp
  refine ⟨_,t,ht,hp,hh,d.work,b,?_,?_,hout⟩
  · exact ⟨⟨b,rfl,hsem,by simpa only [placeWorkCfg_input, hout] using haccepted⟩,hpi,hpw⟩
  · funext j; fin_cases j <;> rfl

theorem middle_stable (src wit : List Bool) : ∀ inp work out,
    middle src wit inp work out → middle src wit (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have horig := h
  obtain ⟨source,prior,hready,hw,ho⟩ := h
  have hwork : ∀ j, (work j).read ≠ .start := by
    rw [hw]; intro j; fin_cases j
    · exact (hready.2.2 0).read_ne_start
    · exact (hready.2.2 1).read_ne_start
    · exact (hready.2.2 2).read_ne_start
    all_goals exact (VerifierReactionLoop.word_parked _).read_ne_start
  have hout : out.read ≠ .start := by rw [ho]; change Γ.blank ≠ Γ.start; decide
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hready.2.1.read_ne_start hwork hout
  simpa only [hi',hw',ho'] using horig

theorem witness_hoare (src wit : List Bool) : VerifierJointWitness.machine.HoareTime
    (middle src wit) (after src wit) (40*(wit.length+1)^2+2*wit.length+18) := by
  rintro inp work out ⟨source,prior,hready,hw,ho⟩
  obtain ⟨d,t,ht,hr,hh,hpost⟩ := VerifierJointWitness.validation_hoare wit source inp prior
    (fun j => (hready.2.2 j).read_ne_start) hready.2.1.read_ne_start
    inp work out ⟨rfl,hw,ho⟩
  have hi := hpost.1
  refine ⟨d,t,ht,hr,hh,source,prior,?_,?_⟩
  · simpa only [hi] using hready
  · simpa only [hi] using hpost

def machine : TM 11 := seqTM sourceMachine VerifierJointWitness.machine

theorem validation_hoare (src wit : List Bool) : machine.HoareTime
    (before src wit) (after src wit) (10*src.length+40*(wit.length+1)^2+2*wit.length+70) := by
  have h := seqTM_hoareTime _ _ (source_hoare src wit) (middle_stable src wit)
    (witness_hoare src wit)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierJointPrepare

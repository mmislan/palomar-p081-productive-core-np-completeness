module

public import proofs.UnconstrainedPACDetection.VerifierMaskNonemptyRouting

@[expose] public section

namespace UnconstrainedPACDetection.VerifierNonemptyCheck
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierFlowPassHoare (ended)

@[reducible] def rewind : TM 4 := placeWorkTM 0 3 (rewindWorkTM (0 : Fin 1))

theorem rewind_hoare (w : BinaryWitnessData.Witness) (frame : Fin 4 → Tape) (inp₀ : Tape) (a : Bool)
    (h0 : frame 0 = ended w.encode) (hf : ∀ j, (frame j).read ≠ .start) (hi : inp₀.read ≠ .start) :
    rewind.HoareTime (VerifierTapeCleanup.frame frame inp₀ (one .start a))
      (VerifierTapeCleanup.frame (Function.update frame 0 (wordTape w.encode)) inp₀ (one .start a))
      (w.encode.length+3) := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst inp; subst work; subst out
  have ho : (one .start a).read ≠ .start := by change Γ.blank ≠ Γ.start; decide
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := VerifierActivationRow.rewind_hoare w.encode w.encode.length inp₀
    (one .start a) hi ho (by change 1 ≤ 2; decide) _ _ _ ⟨rfl,rfl,rfl⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal (rewindWorkTM (0 : Fin 1)) 0 3 frame hd
    (by intro j _; exact hf j)
  refine ⟨placeWorkCfg (rewindWorkTM (0 : Fin 1)) 0 3 frame d,t,ht,?_,hh,hdi,?_,hdo⟩
  · convert hp using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j
      · exact h0
      · rfl
      · rfl
      · rfl
    · rfl
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,hdw]

@[reducible] def machine : TM 4 := seqTM rewind VerifierMaskNonemptyRouting.machine

theorem check_hoare (w : BinaryWitnessData.Witness) (frame : Fin 4 → Tape) (inp₀ : Tape) (a : Bool)
    (h0 : frame 0 = ended w.encode) (hf : ∀ j, (frame j).read ≠ .start) (hi : inp₀.read ≠ .start) :
    machine.HoareTime (VerifierTapeCleanup.frame frame inp₀ (one .start a))
      (fun inp work out => inp = inp₀ ∧
        work 0 = VerifierFlowRestart.flowInput w.mask (VerifierFlowBothSource.flowWire w) ∧
        (∀ j, j ≠ 0 → work j = frame j) ∧ out = one .start (a && w.mask.any id))
      (2*w.encode.length+6) := by
  let next := Function.update frame 0 (wordTape w.encode)
  have hnext : ∀ j, (next j).read ≠ .start := by
    intro j
    by_cases hj : j = 0
    · subst j; exact (Tape.init_move_right_hasBinaryString _).hasBinarySuffix.read_ne_start
    · simpa only [next,Function.update_of_ne hj] using hf j
  have stable : ∀ inp work out, VerifierTapeCleanup.frame next inp₀ (one .start a) inp work out →
      VerifierTapeCleanup.frame next inp₀ (one .start a)
        (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
    rintro inp work out ⟨hin,hwork,hout⟩
    subst inp; subst work; subst out
    exact phaseTransition_eq_self_of_reads_ne_start hi hnext (by change Γ.blank ≠ Γ.start; decide)
  have second := VerifierMaskNonemptyRouting.check_hoare w next inp₀ a (by simp [next]) hnext hi
  have h := seqTM_hoareTime _ _ (rewind_hoare w frame inp₀ a h0 hf hi) stable second
  have hm : 2*w.mask.length+1 ≤ w.encode.length := by
    change 2*w.mask.length+1 ≤ (BinaryFields.encodeField w.mask ++ VerifierFlowBothSource.flowWire w).length
    simp only [List.length_append,BinaryFields.encodeField_length]; omega
  rintro inp work out hp
  obtain ⟨d,t,ht,hd,hh,hdi,hd0,hdf,hdo⟩ := h inp work out hp
  refine ⟨d,t,by omega,hd,hh,hdi,hd0,?_,hdo⟩
  intro j hj
  simpa only [next,Function.update_of_ne hj] using hdf j hj

end UnconstrainedPACDetection.VerifierNonemptyCheck

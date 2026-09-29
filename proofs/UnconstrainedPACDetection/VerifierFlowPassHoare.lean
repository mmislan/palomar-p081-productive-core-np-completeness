module

public import proofs.UnconstrainedPACDetection.VerifierFlowRestart

@[expose] public section

namespace UnconstrainedPACDetection.VerifierFlowPassHoare
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierMaskRestore (fixed)
open VerifierFlowRestart (flowInput)
open VerifierFlowFlagPass (accept)
open VerifierActivationScan (flag)
open VerifierVerdictAnd (one)

def wire (es : List (ℤ × Bool)) : List Bool :=
  BinaryFields.encode (es.map (fun e => BinaryFields.writeInt e.1))

def advance (t : Tape) (k : ℕ) : Tape := {t with head := t.head+k}

theorem advance_suffix (bs tail : List Bool) (wt : Tape) (h : wt.HasBinarySuffix (bs ++ tail)) :
    (advance wt bs.length).HasBinarySuffix tail := by
  induction bs generalizing wt with
  | nil => exact h
  | cons b bs ih =>
    have hh := ih (wt.move .right) h.move_right_cons
    convert hh using 1
    apply Tape.ext
    · simp [advance,Tape.move]; omega
    · rfl

def ended (bits : List Bool) : Tape := ⟨bits.length+1,(wordTape bits).cells⟩

theorem pass_hoare (es : List (ℤ × Bool)) (mask tail : List Bool) (wt : Tape) (m : Γ) (a : Bool)
    (hw : wt.HasBinarySuffix (es.map Prod.snd ++ tail)) :
    VerifierFlowFlags.machine.HoareTime (fixed (flowInput mask (wire es)) wt (flag m a))
      (fixed (ended (BinaryFields.encodeField mask ++ wire es)) (advance wt es.length) (one m (accept es a)))
      ((wire es).length+es.length+1) := by
  rintro i w o ⟨hin,hwork,hout⟩
  subst i; subst w; subst o
  obtain ⟨d,hd,hh,_,hdh,hdc,_,hdwh,hdwc,hdo⟩ := VerifierFlowFlagPass.run es tail
    ⟨(0 : Fin 6),flowInput mask (wire es),fun _ => wt,flag m a⟩ m a rfl
    (VerifierFlowRestart.flowInput_suffix mask (wire es)) hw rfl
  refine ⟨d,_,le_rfl,hd,hh,?_,?_,hdo⟩
  · apply Tape.ext
    · change d.input.head = (BinaryFields.encodeField mask ++ wire es).length+1
      change d.input.head = 2*mask.length+2+(wire es).length at hdh
      simp only [List.length_append,BinaryFields.encodeField_length]; omega
    · exact hdc
  · funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact Tape.ext hdwh (hdwc 0)

theorem fixed_stable (inp wt out : Tape) (hi : inp.read ≠ .start)
    (hw : wt.read ≠ .start) (ho : out.read ≠ .start) :
    ∀ i w o, fixed inp wt out i w o → fixed inp wt out
      (transitionInput i) (fun j => transitionTape (w j)) (transitionTape o) := by
  rintro i w o ⟨hin,hwork,hout⟩
  subst i; subst w; subst o
  exact phaseTransition_eq_self_of_reads_ne_start hi (fun _ => hw) ho

theorem ended_off (bits : List Bool) : (ended bits).read ≠ .start :=
  ((Tape.StartInvariant.init_ofBool bits).move .right).2 (bits.length+1) (by omega)

end UnconstrainedPACDetection.VerifierFlowPassHoare

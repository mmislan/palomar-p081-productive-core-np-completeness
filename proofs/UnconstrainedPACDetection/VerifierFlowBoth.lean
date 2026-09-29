module

public import proofs.UnconstrainedPACDetection.VerifierFlowPassHoare

@[expose] public section

namespace UnconstrainedPACDetection.VerifierFlowBoth
open Complexity Complexity.TM
open VerifierFlowPassHoare (wire advance ended)
open VerifierFlowRestart (flowInput)
open VerifierMaskRestore (fixed)
open VerifierFlowFlagPass (accept)
open VerifierActivationScan (flag)
open VerifierVerdictAnd (one)

def machine : TM 1 := seqTM VerifierFlowFlags.machine
  (seqTM VerifierFlowRestart.machine VerifierFlowFlags.machine)

theorem both_hoare (left right : List (ℤ × Bool)) (mask tail : List Bool) (wt : Tape)
    (m : Γ) (a : Bool) (he : wire right = wire left)
    (hw : wt.HasBinarySuffix (left.map Prod.snd ++ (right.map Prod.snd ++ tail))) :
    machine.HoareTime (fixed (flowInput mask (wire left)) wt (flag m a))
      (fixed (ended (BinaryFields.encodeField mask ++ wire left))
        (advance (advance wt left.length) right.length) (one m (accept right (accept left a))))
      (3*(wire left).length+4*mask.length+left.length+right.length+10) := by
  let wt1 := advance wt left.length
  let v := accept left a
  let lastInput := ended (BinaryFields.encodeField mask ++ wire left)
  have hw1 : wt1.HasBinarySuffix (right.map Prod.snd ++ tail) := by
    simpa only [List.length_map] using VerifierFlowPassHoare.advance_suffix
      (left.map Prod.snd) (right.map Prod.snd ++ tail) wt hw
  have hor : (one m v).read ≠ .start := by change Γ.blank ≠ Γ.start; decide
  have hflag : (flag m v).read ≠ .start := by
    change Γ.ofBool v ≠ .start; cases v <;> decide
  have restart := VerifierFlowRestart.restart_hoare mask (wire left) lastInput wt1 m v rfl
    hw1.read_ne_start hw1.1
  have second := VerifierFlowPassHoare.pass_hoare right mask tail wt1 m v hw1
  rw [he] at second
  have middle := seqTM_hoareTime _ _ restart
    (VerifierFlowPassHoare.fixed_stable _ wt1 (flag m v)
      (VerifierFlowRestart.flowInput_suffix mask (wire left)).read_ne_start hw1.read_ne_start hflag) second
  have first := VerifierFlowPassHoare.pass_hoare left mask (right.map Prod.snd ++ tail) wt m a hw
  have h := seqTM_hoareTime _ _ first
    (VerifierFlowPassHoare.fixed_stable lastInput wt1 (one m v)
      (VerifierFlowPassHoare.ended_off _) hw1.read_ne_start hor) middle
  apply h.mono_bound
  simp only [lastInput,ended,List.length_append,BinaryFields.encodeField_length]
  omega

end UnconstrainedPACDetection.VerifierFlowBoth

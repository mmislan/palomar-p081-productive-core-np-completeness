module

public import proofs.UnconstrainedPACDetection.VerifierTraversalAdvance

@[expose] public section

/-! One nonfinal reaction: contribution, source stride, and flow-index advance. -/
namespace UnconstrainedPACDetection.VerifierReactionStep
open Complexity
open Complexity.TM
open VerifierIndexedField (counter)
open VerifierTraversalContribution (extend pred)
open VerifierSignedContribution (newPos newNeg)
open VerifierTraversalAdvance (stable frame_off)

theorem stride_hoare (k : ℕ) (wit : Tape) (pos neg : List Bool) (skipped : List (List Bool))
    (suffix : List Bool) (loop out₀ : Tape) (hi : wit.read ≠ .start) (hlp : loop.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    VerifierSourceStride.machine.HoareTime
      (pred k wit pos neg (BinaryFields.encode skipped ++ suffix) (counter skipped.length) loop out₀)
      (pred k wit pos neg suffix (counter skipped.length) loop out₀)
      ((BinaryFields.encode skipped).length+2*skipped.length+5) := by
  exact VerifierSourceStride.stride_hoare skipped suffix
    (extend (VerifierCoefficientIteration.layout [] k wit pos neg) (counter skipped.length) loop) out₀ rfl
    (fun j _ => frame_off k wit pos neg (counter skipped.length) loop hi
      (Tape.init_move_right_hasBinaryString _).hasBinarySuffix.read_ne_start hlp j) ho hoh

def moveNext : TM 11 := seqTM VerifierSourceStride.machine VerifierTraversalAdvance.machine

theorem moveNext_hoare (k : ℕ) (wit : Tape) (pos neg : List Bool) (skipped : List (List Bool))
    (suffix : List Bool) (loop out₀ : Tape) (hi : wit.read ≠ .start) (hwh : wit.head = 1)
    (hlp : loop.read ≠ .start) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    moveNext.HoareTime
      (pred k wit pos neg (BinaryFields.encode skipped ++ suffix) (counter skipped.length) loop out₀)
      (pred (k+1) wit pos neg suffix (counter skipped.length) loop out₀)
      ((BinaryFields.encode skipped).length+2*skipped.length+2*k+12) := by
  have hst := (Tape.init_move_right_hasBinaryString (List.replicate skipped.length true)).hasBinarySuffix.read_ne_start
  have h := seqTM_hoareTime _ _ (stride_hoare k wit pos neg skipped suffix loop out₀ hi hlp ho hoh)
    (stable k wit pos neg suffix (counter skipped.length) loop out₀ hi hst hlp ho)
    (VerifierTraversalAdvance.advance_hoare k wit pos neg suffix (counter skipped.length) loop out₀ hi hwh hst hlp ho hoh)
  exact h.mono_bound (by omega)

def machine (isRight : Bool) := seqTM (VerifierTraversalContribution.machine isRight) moveNext

theorem reaction_step_hoare (isRight : Bool) (fields skipped : List (List Bool)) (xs : List Bool) (sign : Bool)
    (mag pos neg sourceSuffix witnessSuffix : List Bool) (wit loop out₀ : Tape)
    (hi : wit.HasBinarySuffix (BinaryFields.encode fields ++ (BinaryFields.encodeField (sign :: mag) ++ witnessSuffix)))
    (hm : wit.StartInvariant) (hwh : wit.head = 1) (hlp : loop.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (machine isRight).HoareTime
      (pred fields.length wit pos neg
        (BinaryFields.encodeField xs ++ (BinaryFields.encode skipped ++ sourceSuffix))
        (counter skipped.length) loop out₀)
      (pred (fields.length+1) wit
        (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos)
        (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg)
        sourceSuffix (counter skipped.length) loop out₀)
      (2*VerifierContributionIteration.contributionBound fields xs mag pos neg+5*xs.length+2*mag.length+
        2*(VerifierBinaryProduct.multiply xs mag).length+(BinaryFields.encode skipped).length+
        2*skipped.length+3*fields.length+53) := by
  have hst := (Tape.init_move_right_hasBinaryString (List.replicate skipped.length true)).hasBinarySuffix.read_ne_start
  have h := seqTM_hoareTime _ _
    (VerifierTraversalContribution.contribution_hoare isRight fields xs sign mag pos neg
      (BinaryFields.encode skipped ++ sourceSuffix) witnessSuffix wit (counter skipped.length) loop out₀
      hi hm hwh hst hlp ho hoh)
    (stable fields.length wit
      (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos)
      (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg)
      (BinaryFields.encode skipped ++ sourceSuffix) (counter skipped.length) loop out₀ hi.read_ne_start hst hlp ho)
    (moveNext_hoare fields.length wit
      (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos)
      (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg)
      skipped sourceSuffix loop out₀ hi.read_ne_start hwh hlp ho hoh)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierReactionStep

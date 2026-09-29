module

public import proofs.UnconstrainedPACDetection.VerifierContributionIteration

@[expose] public section

/-! Read a real source coefficient, execute its signed contribution, and reset. -/
namespace UnconstrainedPACDetection.VerifierCoefficientIteration
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierSignedContribution (extend newPos newNeg)

def layout (xs : List Bool) (k : ℕ) (wit : Tape) (pos neg : List Bool) :=
  extend (VerifierWitnessProduct.initial xs k wit) pos neg
@[reducible] def pred (xs : List Bool) (k : ℕ) (wit : Tape) (pos neg suffix : List Bool) (out₀ : Tape) :
    Tape → (Fin 9 → Tape) → Tape → Prop :=
  fun inp work out => inp.HasBinarySuffix suffix ∧ work = layout xs k wit pos neg ∧ out = out₀

theorem layout_off (xs : List Bool) (k : ℕ) (wit : Tape) (pos neg : List Bool)
    (hi : wit.read ≠ .start) : ∀ j, (layout xs k wit pos neg j).read ≠ .start := by
  intro j
  fin_cases j
  · exact (Tape.init_move_right_hasBinaryString xs).hasBinarySuffix.read_ne_start
  · exact (Tape.init_move_right_hasBinaryString (List.replicate k true)).hasBinarySuffix.read_ne_start
  · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start
  · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start
  · exact hi
  · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start
  · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start
  · exact (Tape.init_move_right_hasBinaryString pos).hasBinarySuffix.read_ne_start
  · exact (Tape.init_move_right_hasBinaryString neg).hasBinarySuffix.read_ne_start

def parse : TM 9 := VerifierFieldPlacement.machine 0 8

theorem parse_hoare (xs : List Bool) (k : ℕ) (wit : Tape) (pos neg suffix : List Bool) (out₀ : Tape)
    (hi : wit.read ≠ .start) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    parse.HoareTime (pred [] k wit pos neg (BinaryFields.encodeField xs ++ suffix) out₀)
      (pred xs k wit pos neg suffix out₀) (3*xs.length+5) := by
  have h := VerifierFieldPlacement.field_hoare 0 8 xs suffix (layout [] k wit pos neg) out₀ rfl
    (fun j _ => layout_off [] k wit pos neg hi j) ho hoh
  have he : Function.update (layout [] k wit pos neg) (VerifierFieldPlacement.slot 0 8) (wordTape xs) =
      layout xs k wit pos neg := by
    funext j
    fin_cases j <;> simp [layout,extend,VerifierWitnessProduct.initial,
      VerifierFieldPlacement.slot,placeWorkIdx]
  simpa [parse, pred, he] using h

theorem compute_hoare (isRight : Bool) (fields : List (List Bool)) (xs : List Bool) (sign : Bool)
    (mag pos neg sourceSuffix witnessSuffix : List Bool) (wit out₀ : Tape)
    (hi : wit.HasBinarySuffix (BinaryFields.encode fields ++ (BinaryFields.encodeField (sign :: mag) ++ witnessSuffix)))
    (hm : wit.StartInvariant) (hwh : wit.head = 1) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (VerifierContributionIteration.machine isRight).HoareTime
      (pred xs fields.length wit pos neg sourceSuffix out₀)
      (pred [] fields.length wit
        (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos)
        (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg) sourceSuffix out₀)
      (2*VerifierContributionIteration.contributionBound fields xs mag pos neg+2*xs.length+2*mag.length+
        2*(VerifierBinaryProduct.multiply xs mag).length+fields.length+34) := by
  rintro inp work out ⟨hs,hw,hout⟩
  subst work
  subst out
  obtain ⟨d,t,hb,hd,hh,hin,hdw,hout⟩ := VerifierContributionIteration.iteration_hoare isRight fields xs sign
    mag pos neg witnessSuffix wit inp out₀ hi hm hwh hs.read_ne_start ho hoh
    inp (layout xs fields.length wit pos neg) out₀ ⟨rfl,rfl,rfl⟩
  exact ⟨d,t,hb,hd,hh,hin ▸ hs,hdw,hout⟩

def machine (isRight : Bool) := seqTM parse (VerifierContributionIteration.machine isRight)

theorem coefficient_iteration_hoare (isRight : Bool) (fields : List (List Bool)) (xs : List Bool) (sign : Bool)
    (mag pos neg sourceSuffix witnessSuffix : List Bool) (wit out₀ : Tape)
    (hi : wit.HasBinarySuffix (BinaryFields.encode fields ++ (BinaryFields.encodeField (sign :: mag) ++ witnessSuffix)))
    (hm : wit.StartInvariant) (hwh : wit.head = 1) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (machine isRight).HoareTime
      (pred [] fields.length wit pos neg (BinaryFields.encodeField xs ++ sourceSuffix) out₀)
      (pred [] fields.length wit
        (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos)
        (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg) sourceSuffix out₀)
      (2*VerifierContributionIteration.contributionBound fields xs mag pos neg+5*xs.length+2*mag.length+
        2*(VerifierBinaryProduct.multiply xs mag).length+fields.length+40) := by
  have stable : ∀ inp work out, pred xs fields.length wit pos neg sourceSuffix out₀ inp work out →
      pred xs fields.length wit pos neg sourceSuffix out₀ (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
    rintro inp work out ⟨hs,rfl,rfl⟩
    obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start hs.read_ne_start
      (layout_off xs fields.length wit pos neg hi.read_ne_start) ho
    exact ⟨by simpa only [hin] using hs,hw,hout⟩
  have h := seqTM_hoareTime _ _ (parse_hoare xs fields.length wit pos neg sourceSuffix out₀ hi.read_ne_start ho hoh)
    stable (compute_hoare isRight fields xs sign mag pos neg sourceSuffix witnessSuffix wit out₀ hi hm hwh ho hoh)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierCoefficientIteration

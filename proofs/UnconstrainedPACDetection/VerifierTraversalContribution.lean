module

public import proofs.UnconstrainedPACDetection.VerifierCoefficientIteration
public import proofs.UnconstrainedPACDetection.VerifierSourceStride

@[expose] public section

/-! Preserve stride and reaction-loop tapes while executing the full contribution. -/
namespace UnconstrainedPACDetection.VerifierTraversalContribution
open Complexity
open Complexity.TM
open VerifierSignedContribution (newPos newNeg)
open VerifierCoefficientIteration (layout)

def extend (w : Fin 9 → Tape) (stride loop : Tape) : Fin 11 → Tape :=
  ![w 0,w 1,w 2,w 3,w 4,w 5,w 6,w 7,w 8,stride,loop]

def pred (k : ℕ) (wit : Tape) (pos neg suffix : List Bool) (stride loop out₀ : Tape) :
    Tape → (Fin 11 → Tape) → Tape → Prop :=
  fun inp work out => inp.HasBinarySuffix suffix ∧ work = extend (layout [] k wit pos neg) stride loop ∧ out = out₀

def machine (isRight : Bool) : TM 11 := placeWorkTM 0 2 (VerifierCoefficientIteration.machine isRight)

theorem contribution_hoare (isRight : Bool) (fields : List (List Bool)) (xs : List Bool) (sign : Bool)
    (mag pos neg sourceSuffix witnessSuffix : List Bool) (wit stride loop out₀ : Tape)
    (hi : wit.HasBinarySuffix (BinaryFields.encode fields ++ (BinaryFields.encodeField (sign :: mag) ++ witnessSuffix)))
    (hm : wit.StartInvariant) (hwh : wit.head = 1)
    (hst : stride.read ≠ .start) (hlp : loop.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (machine isRight).HoareTime
      (pred fields.length wit pos neg (BinaryFields.encodeField xs ++ sourceSuffix) stride loop out₀)
      (pred fields.length wit
        (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos)
        (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg) sourceSuffix stride loop out₀)
      (2*VerifierContributionIteration.contributionBound fields xs mag pos neg+5*xs.length+2*mag.length+
        2*(VerifierBinaryProduct.multiply xs mag).length+fields.length+40) := by
  rintro inp work out ⟨hs,hw,hout⟩
  subst work
  subst out
  let w := layout [] fields.length wit pos neg
  obtain ⟨d,t,hb,hd,hh,hin,hdw,hout⟩ := VerifierCoefficientIteration.coefficient_iteration_hoare
    isRight fields xs sign mag pos neg sourceSuffix witnessSuffix wit out₀ hi hm hwh ho hoh
    inp w out₀ ⟨hs,rfl,rfl⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    (VerifierCoefficientIteration.machine isRight) 0 2 (extend w stride loop) hd (by
      intro j hj
      fin_cases j
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · exact hst
      · exact hlp)
  have he : placeWorkCfg (VerifierCoefficientIteration.machine isRight) 0 2 (extend w stride loop)
      ⟨(VerifierCoefficientIteration.machine isRight).qstart,inp,w,out₀⟩ =
      (⟨(machine isRight).qstart,inp,extend w stride loop,out₀⟩ : Cfg 11 (machine isRight).Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,extend]
    · rfl
  refine ⟨placeWorkCfg (VerifierCoefficientIteration.machine isRight) 0 2 (extend w stride loop) d,
    t,hb,?_,hh,hin,?_,hout⟩
  · change (machine isRight).reachesIn _ _ _ at hp
    simpa only [he] using hp
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,extend,hdw]

end UnconstrainedPACDetection.VerifierTraversalContribution

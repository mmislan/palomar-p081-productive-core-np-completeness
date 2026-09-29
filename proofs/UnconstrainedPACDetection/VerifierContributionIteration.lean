module

public import proofs.UnconstrainedPACDetection.VerifierContributionRewind

@[expose] public section

/-! A charged signed contribution followed by full buffer/cursor reset. -/
namespace UnconstrainedPACDetection.VerifierContributionIteration
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierSignedContribution (ready result extend newPos newNeg addBound)

def boundedResult (xs : List Bool) (k : ℕ) (sign : Bool) (mag prod pos neg suffix : List Bool)
    (wit₀ inp₀ out₀ : Tape) (H : ℕ) : Tape → (Fin 9 → Tape) → Tape → Prop :=
  fun inp work out => result xs k sign mag prod pos neg suffix wit₀ inp₀ out₀ inp work out ∧
    (work 4).head ≤ H

theorem reset_hoare (xs : List Bool) (k : ℕ) (sign : Bool) (mag prod pos neg suffix : List Bool)
    (wit₀ inp₀ out₀ : Tape) (H : ℕ) (hm : wit₀.StartInvariant) (hwh : wit₀.head = 1)
    (hr : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    VerifierContributionRewind.reuse.HoareTime
      (boundedResult xs k sign mag prod pos neg suffix wit₀ inp₀ out₀ H)
      (VerifierContributionReset.frame (extend (VerifierWitnessProduct.initial [] k wit₀) pos neg) inp₀ out₀)
      (2*xs.length+2*mag.length+2*prod.length+k+H+32) := by
  rintro inp work out ⟨⟨hin,wit,hwi,hwc,hwork,hout⟩,hbound⟩
  subst inp
  subst work
  subst out
  have hwm : wit.StartInvariant := by
    change wit.cells 0 = .start ∧ ∀ j, 1 ≤ j → wit.cells j ≠ .start
    rw [hwc]
    exact hm
  have hhead : 1 ≤ wit.head := by
    have hn := hwi.read_ne_start
    have hz := hwm.1
    by_contra h
    have he : wit.head = 0 := by omega
    exact hn (by simpa [Tape.read,he] using hz)
  have hs : VerifierContributionReset.safe (ready xs k sign mag prod pos neg wit) := by
    intro j
    refine ⟨VerifierSignedContribution.ready_off xs k sign mag prod pos neg suffix wit hwi j,?_⟩
    fin_cases j <;> first | exact hhead | simp [ready,extend,VerifierWitnessProduct.ready,
      VerifierIndexedField.exhausted,wordTape,Tape.move]
  have hcounter := (Tape.StartInvariant.init_ofBool (List.replicate k true)).move .right
  have h := VerifierContributionRewind.reuse_hoare xs mag prod sign
    (ready xs k sign mag prod pos neg wit) inp₀ out₀ rfl rfl rfl rfl
    hcounter.1 hcounter.2 hwm.1 hwm.2 hs hr ho hoh
  obtain ⟨d,t,hb,hd,hh,hin,hw,hout⟩ := h inp₀ (ready xs k sign mag prod pos neg wit) out₀ ⟨rfl,rfl,rfl⟩
  have he : (⟨1,wit.cells⟩ : Tape) = wit₀ := Tape.ext hwh.symm hwc
  refine ⟨d,t,?_,hd,hh,hin,?_,hout⟩
  · change wit.head ≤ H at hbound
    change t ≤ 2*xs.length+2*mag.length+2*prod.length+(k+1)+wit.head+31 at hb
    omega
  · rw [hw]
    funext j
    fin_cases j <;> simp [VerifierContributionRewind.restored,VerifierContributionReset.after,
      VerifierContributionReset.cleared,ready,extend,VerifierWitnessProduct.ready,
      VerifierWitnessProduct.initial,VerifierIndexedField.exhausted,VerifierIndexedField.counter,he]
    all_goals exact Tape.ext (by rfl) rfl

def contributionBound (fields : List (List Bool)) (xs mag pos neg : List Bool) : ℕ :=
  (BinaryFields.encode fields).length+fields.length+4*mag.length+14+
    mag.length*(10*xs.length+20*mag.length+30)+addBound (VerifierBinaryProduct.multiply xs mag) pos neg

theorem bounded_contribution (isRight : Bool) (fields : List (List Bool)) (xs : List Bool) (sign : Bool)
    (mag pos neg suffix : List Bool) (wit₀ inp₀ out₀ : Tape)
    (hi : wit₀.HasBinarySuffix (BinaryFields.encode fields ++ (BinaryFields.encodeField (sign :: mag) ++ suffix)))
    (hm : wit₀.StartInvariant) (hr : inp₀.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (VerifierSignedContribution.machine isRight).HoareTime
      (VerifierContributionReset.frame (extend (VerifierWitnessProduct.initial xs fields.length wit₀) pos neg) inp₀ out₀)
      (boundedResult xs fields.length sign mag (VerifierBinaryProduct.multiply xs mag)
        (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos)
        (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg) suffix wit₀ inp₀ out₀
        (wit₀.head+contributionBound fields xs mag pos neg))
      (contributionBound fields xs mag pos neg) := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst inp
  subst work
  subst out
  obtain ⟨d,t,hb,hd,hh,hres⟩ := VerifierSignedContribution.contribution_hoare isRight fields xs sign
    mag pos neg suffix wit₀ inp₀ out₀ hi hm hr ho hoh
    inp₀ (extend (VerifierWitnessProduct.initial xs fields.length wit₀) pos neg) out₀ ⟨rfl,rfl,rfl⟩
  have hhbound := (VerifierSignedContribution.machine isRight).work_head_reachesIn_bound hd 4
  change (d.work 4).head ≤ wit₀.head+t at hhbound
  exact ⟨d,t,hb,hd,hh,hres,hhbound.trans (Nat.add_le_add_left hb _)⟩

def machine (isRight : Bool) := seqTM (VerifierSignedContribution.machine isRight) VerifierContributionRewind.reuse

theorem iteration_hoare (isRight : Bool) (fields : List (List Bool)) (xs : List Bool) (sign : Bool)
    (mag pos neg suffix : List Bool) (wit₀ inp₀ out₀ : Tape)
    (hi : wit₀.HasBinarySuffix (BinaryFields.encode fields ++ (BinaryFields.encodeField (sign :: mag) ++ suffix)))
    (hm : wit₀.StartInvariant) (hwh : wit₀.head = 1) (hr : inp₀.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoh : 1 ≤ out₀.head) :
    (machine isRight).HoareTime
      (VerifierContributionReset.frame (extend (VerifierWitnessProduct.initial xs fields.length wit₀) pos neg) inp₀ out₀)
      (VerifierContributionReset.frame (extend (VerifierWitnessProduct.initial [] fields.length wit₀)
        (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos)
        (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg)) inp₀ out₀)
      (2*contributionBound fields xs mag pos neg+2*xs.length+2*mag.length+
        2*(VerifierBinaryProduct.multiply xs mag).length+fields.length+34) := by
  have stable : ∀ inp work out,
      boundedResult xs fields.length sign mag (VerifierBinaryProduct.multiply xs mag)
        (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos)
        (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg) suffix wit₀ inp₀ out₀
        (wit₀.head+contributionBound fields xs mag pos neg) inp work out →
      boundedResult xs fields.length sign mag (VerifierBinaryProduct.multiply xs mag)
        (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos)
        (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg) suffix wit₀ inp₀ out₀
        (wit₀.head+contributionBound fields xs mag pos neg)
        (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
    rintro inp work out ⟨⟨rfl,wit,hwi,hwc,rfl,rfl⟩,hb⟩
    obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start hr
      (VerifierSignedContribution.ready_off _ _ _ _ _ _ _ suffix wit hwi) ho
    have h4 := congrFun hw 4
    exact ⟨⟨hin,wit,hwi,hwc,hw,hout⟩,(congrArg Tape.head h4).le.trans hb⟩
  have h := seqTM_hoareTime _ _ (bounded_contribution isRight fields xs sign mag pos neg suffix wit₀ inp₀ out₀ hi hm hr ho hoh)
    stable (reset_hoare xs fields.length sign mag (VerifierBinaryProduct.multiply xs mag)
      (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos)
      (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg) suffix wit₀ inp₀ out₀
      (wit₀.head+contributionBound fields xs mag pos neg) hm hwh hr ho hoh)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierContributionIteration

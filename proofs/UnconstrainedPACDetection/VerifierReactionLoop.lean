module

public import proofs.UnconstrainedPACDetection.VerifierMovingInputLoop
public import proofs.UnconstrainedPACDetection.VerifierReactionStep

@[expose] public section

/-! A complete counted execution of nonfinal reaction bodies, with source-suffix
and arithmetic invariants supplied for the intended traversal. -/
namespace UnconstrainedPACDetection.VerifierReactionLoop
open Complexity Complexity.TM
open VerifierTraversalContribution (extend)
open VerifierCoefficientIteration (layout)
open VerifierIndexedField (counter)
open VerifierBufferedProduct (wordTape)
open VerifierSignedContribution (newPos newNeg)

theorem update_loop (w : Fin 9 → Tape) (stride old next : Tape) :
    Function.update (extend w stride old) 10 next = extend w stride next := by
  funext j
  fin_cases j <;> simp [extend]

def frame (k stride fuel : ℕ) (wit : Tape) (pos neg : List Bool) : Fin 11 → Tape :=
  extend (layout [] k wit pos neg) (counter stride) (regTape fuel)

theorem word_parked (xs : List Bool) : Parked (wordTape xs) :=
  ⟨by rfl, fun j hj => ((Tape.StartInvariant.init_ofBool xs).move .right).2 j (by omega)⟩

theorem frame_parked (k stride fuel : ℕ) (wit : Tape) (pos neg : List Bool)
    (hw : Parked wit) : ∀ j, Parked (frame k stride fuel wit pos neg j) := by
  intro j
  fin_cases j <;>
    simp only [frame,extend,layout,VerifierSignedContribution.extend,
      VerifierWitnessProduct.initial,Matrix.cons_val_zero]
  all_goals first | exact word_parked _ | exact hw | exact parked_regTape _

def sourcePred (suffix : List Bool) (inp : Tape) :=
  inp.HasBinarySuffix suffix

theorem source_parked (suffix : List Bool) (inp : Tape) (h : sourcePred suffix inp) :
    Parked inp := ⟨h.1,h.2.2.2⟩

def bodyBound (fields skipped : List (List Bool)) (xs mag pos neg : List Bool) :=
  2*VerifierContributionIteration.contributionBound fields xs mag pos neg+5*xs.length+2*mag.length+
    2*(VerifierBinaryProduct.multiply xs mag).length+(BinaryFields.encode skipped).length+
    2*skipped.length+3*fields.length+53

/-- The actual repeated reaction machine, not an abstract iteration oracle.
The uniform body bound and semantic recurrences remain explicit hypotheses. -/
theorem reactions_hoare (b : Bool) (v k stride B : ℕ) (wit : Tape)
    (fields skipped : ℕ → List (List Bool))
    (xs mag suffix witSuffix pos neg : ℕ → List Bool) (sign : ℕ → Bool)
    (hw : wit.StartInvariant) (hwh : wit.head = 1)
    (hfields : ∀ i, i < v → (fields i).length = k+i)
    (hskip : ∀ i, i < v → (skipped i).length = stride)
    (hwit : ∀ i, i < v → wit.HasBinarySuffix
      (BinaryFields.encode (fields i) ++
        (BinaryFields.encodeField (sign i :: mag i) ++ witSuffix i)))
    (hsource : ∀ i, i < v → suffix i = BinaryFields.encodeField (xs i) ++
      (BinaryFields.encode (skipped i) ++ suffix (i+1)))
    (hpos : ∀ i, i < v → pos (i+1) =
      newPos (xor b (sign i)) (VerifierBinaryProduct.multiply (xs i) (mag i)) (pos i))
    (hneg : ∀ i, i < v → neg (i+1) =
      newNeg (xor b (sign i)) (VerifierBinaryProduct.multiply (xs i) (mag i)) (neg i))
    (hbound : ∀ i, i < v → bodyBound (fields i) (skipped i) (xs i) (mag i) (pos i) (neg i) ≤ B) :
    (forRegTM (VerifierReactionStep.machine b) 10).HoareTime
      (fun inp work out => sourcePred (suffix 0) inp ∧
        work = frame k stride v wit (pos 0) (neg 0) ∧ OutAcc [] out)
      (fun inp work out => sourcePred (suffix v) inp ∧
        work = frame (k+v) stride v wit (pos v) (neg v) ∧ OutAcc [] out)
      (v*(B+2)+(v+2)) := by
  have hwp : Parked wit := ⟨by omega, fun j hj => hw.2 j (by omega)⟩
  have hbody : ∀ i, i < v → (VerifierReactionStep.machine b).HoareTime
      (fun inp work out => sourcePred (suffix i) inp ∧
        work = Function.update (frame (k+i) stride v wit (pos i) (neg i)) 10
          ⟨i+2,regCells v⟩ ∧ OutAcc [] out)
      (fun inp work out => sourcePred (suffix (i+1)) inp ∧
        work = Function.update (frame (k+(i+1)) stride v wit (pos (i+1)) (neg (i+1))) 10
          ⟨i+2,regCells v⟩ ∧ OutAcc [] out) B := by
    intro i hi inp work out h
    let fuel : Tape := ⟨i+2,regCells v⟩
    have hfp : Parked fuel := ⟨by dsimp [fuel]; omega, fun j hj => by
      change regCells v j ≠ .start
      rw [regCells,ite_eq_right (by omega)]
      split <;> decide⟩
    have hs := VerifierReactionStep.reaction_step_hoare b (fields i) (skipped i) (xs i)
      (sign i) (mag i) (pos i) (neg i) (suffix (i+1)) (witSuffix i) wit fuel out
      (hwit i hi) hw hwh hfp.read_ne_start h.2.2.parked.read_ne_start h.2.2.parked.1
    rw [hfields i hi,hskip i hi] at hs
    have hin : VerifierTraversalContribution.pred (k+i) wit (pos i) (neg i)
        (BinaryFields.encodeField (xs i) ++ (BinaryFields.encode (skipped i) ++ suffix (i+1)))
        (counter stride) fuel out inp work out := by
      refine ⟨?_,?_,rfl⟩
      · rw [← hsource i hi]; exact h.1
      · simpa only [frame,update_loop] using h.2.1
    obtain ⟨c,t,ht,hr,hh,hsuf,hwc,hout⟩ := hs inp work out hin
    refine ⟨c,t,?_,hr,hh,hsuf,?_,?_⟩
    · have hb := hbound i hi
      dsimp [bodyBound] at hb
      rw [hfields i hi,hskip i hi] at hb
      exact ht.trans hb
    · simpa only [frame,update_loop,hpos i hi,hneg i hi,Nat.add_assoc] using hwc
    · rw [hout]; exact h.2.2
  have hloop := VerifierMovingInputLoop.input_predicate_hoareTime
    (VerifierReactionStep.machine b) 10 v (fun i => sourcePred (suffix i))
    (fun i => frame (k+i) stride v wit (pos i) (neg i)) (fun _ => []) B
    (fun i inp hi => source_parked (suffix i) inp hi)
    (fun _ => rfl) (fun i j _ => frame_parked (k+i) stride v wit (pos i) (neg i) hwp j) hbody
  simpa only [Nat.add_zero] using hloop

end UnconstrainedPACDetection.VerifierReactionLoop

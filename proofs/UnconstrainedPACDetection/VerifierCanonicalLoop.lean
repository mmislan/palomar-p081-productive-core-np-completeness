module

public import proofs.UnconstrainedPACDetection.VerifierReactionBudget
public import proofs.UnconstrainedPACDetection.VerifierCanonicalContribution
public import proofs.UnconstrainedPACDetection.VerifierStrideCoordinates

@[expose] public section

namespace UnconstrainedPACDetection.VerifierCanonicalLoop
open Complexity Complexity.TM
open VerifierCanonicalCoordinates
open VerifierCanonicalContribution (sign magnitude product)
open VerifierReactionLoop (frame sourcePred)
open VerifierBufferedProduct (wordTape)
open VerifierSignedContribution (newPos newNeg)

def reaction (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions) (i : ℕ) : Fin s.reactions :=
  ⟨min i (s.reactions-1),lt_of_le_of_lt (min_le_right _ _) (by omega)⟩

theorem reaction_val (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (i : ℕ) (hi : i < s.reactions) : (reaction s hn i).val = i := by
  exact min_eq_left (by omega)

def suffix (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (b : Bool) (x : Fin s.entities) (i : ℕ) :=
  BinaryFields.encodeField (coefficient s b (reaction s hn i) x).bits ++
    sourceSuffix s b (reaction s hn i) x

theorem suffix_next (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (b : Bool) (x : Fin s.entities) (i : ℕ) (hi : i < s.reactions-1) :
    suffix s hn b x i =
      BinaryFields.encodeField (coefficient s b (reaction s hn i) x).bits ++
        (BinaryFields.encode (VerifierStrideCoordinates.skipped s b (reaction s hn i) x) ++
          suffix s hn b x (i+1)) := by
  have he : (reaction s hn (i+1)).val = (reaction s hn i).val+1 := by
    rw [reaction_val s hn i (by omega),reaction_val s hn (i+1) (by omega)]
  have h := (VerifierStrideCoordinates.source_successor s hs b
    (reaction s hn i) (reaction s hn (i+1)) x he).2
  exact congrArg (fun tail => BinaryFields.encodeField
    (coefficient s b (reaction s hn i) x).bits ++ tail) h

/-- Actual canonical traversal through all nonfinal reactions at a fixed entity.
Totals are specified by their exact recurrence; B is the uniform body budget. -/
theorem canonical_loop (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (b : Bool) (x : Fin s.entities)
    (w : BinaryWitnessData.Witness) (hw : w.flow.length = s.reactions)
    (pos neg : ℕ → List Bool) (B : ℕ)
    (hpos : ∀ i, i < s.reactions-1 → pos (i+1) =
      newPos (xor b (sign w i)) (product s b (reaction s hn i) x w) (pos i))
    (hneg : ∀ i, i < s.reactions-1 → neg (i+1) =
      newNeg (xor b (sign w i)) (product s b (reaction s hn i) x w) (neg i))
    (hbound : ∀ i, i < s.reactions-1 →
      VerifierReactionLoop.bodyBound (witnessPrefix w i)
        (VerifierStrideCoordinates.skipped s b (reaction s hn i) x)
        (coefficient s b (reaction s hn i) x).bits (magnitude w i) (pos i) (neg i) ≤ B) :
    (forRegTM (VerifierReactionStep.machine b) 10).HoareTime
      (fun inp work out => sourcePred (suffix s hn b x 0) inp ∧
        work = frame 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) (pos 0) (neg 0) ∧ OutAcc [] out)
      (fun inp work out => sourcePred (suffix s hn b x (s.reactions-1)) inp ∧
        work = frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode)
          (pos (s.reactions-1)) (neg (s.reactions-1)) ∧ OutAcc [] out)
      ((s.reactions-1)*(B+2)+(s.reactions-1+2)) := by
  have h := VerifierReactionLoop.reactions_hoare b (s.reactions-1) 1 (s.entities-1) B
    (wordTape w.encode) (witnessPrefix w)
    (fun i => VerifierStrideCoordinates.skipped s b (reaction s hn i) x)
    (fun i => (coefficient s b (reaction s hn i) x).bits) (magnitude w)
    (suffix s hn b x) (witnessSuffix w) pos neg (sign w)
    ((Tape.StartInvariant.init_ofBool w.encode).move .right) rfl
    (fun i hi => witnessPrefix_length w i (by rw [hw]; omega))
    (fun i hi => ?_) (fun i hi => ?_) (suffix_next s hs hn b x)
    (fun i hi => ?_) (fun i hi => ?_) hbound
  · simpa only [show 1+(s.reactions-1) = s.reactions from by omega] using h
  · exact (VerifierStrideCoordinates.source_successor s hs b
      (reaction s hn i) (reaction s hn (i+1)) x (by
        rw [reaction_val s hn i (by omega),reaction_val s hn (i+1) (by omega)])).1
  · have hr : i < w.flow.length := by rw [hw]; omega
    unfold VerifierBufferedProduct.wordTape
    change ((Tape.init (w.encode.map Γ.ofBool)).move .right).HasBinarySuffix
      (BinaryFields.encode (witnessPrefix w i) ++
        (BinaryFields.encodeField (BinaryFields.writeInt (w.flow.getD i 0)) ++
          witnessSuffix w i))
    rw [← witness_split w i hr]
    exact (Tape.init_move_right_hasBinaryString w.encode).hasBinarySuffix
  · simpa only [product,reaction_val s hn i (by omega)] using hpos i hi
  · simpa only [product,reaction_val s hn i (by omega)] using hneg i hi

end UnconstrainedPACDetection.VerifierCanonicalLoop

module

public import proofs.UnconstrainedPACDetection.VerifierCanonicalLoop

@[expose] public section

namespace UnconstrainedPACDetection.VerifierCanonicalPhase
open Complexity Complexity.TM
open VerifierCanonicalCoordinates
open VerifierCanonicalContribution (sign magnitude product)
open VerifierCanonicalLoop (reaction suffix)
open VerifierReactionLoop (frame sourcePred)
open VerifierBufferedProduct (wordTape)
open VerifierSignedContribution (newPos newNeg)

def machine (b : Bool) : TM 11 := seqTM
  (forRegTM (VerifierReactionStep.machine b) 10) (VerifierTraversalContribution.machine b)

def finalCost (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (b : Bool) (x : Fin s.entities) (w : BinaryWitnessData.Witness) (pos neg : List Bool) :=
  let r := s.reactions-1
  let xs := (coefficient s b (reaction s hn r) x).bits
  2*VerifierContributionIteration.contributionBound (witnessPrefix w r) xs (magnitude w r) pos neg+
    5*xs.length+2*(magnitude w r).length+2*(product s b (reaction s hn r) x w).length+r+41

theorem phase_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (b : Bool) (x : Fin s.entities)
    (w : BinaryWitnessData.Witness) (hw : w.flow.length = s.reactions)
    (pos neg : ℕ → List Bool) (B : ℕ)
    (hpos : ∀ i, i < s.reactions → pos (i+1) =
      newPos (xor b (sign w i)) (product s b (reaction s hn i) x w) (pos i))
    (hneg : ∀ i, i < s.reactions → neg (i+1) =
      newNeg (xor b (sign w i)) (product s b (reaction s hn i) x w) (neg i))
    (hbound : ∀ i, i < s.reactions-1 →
      VerifierReactionLoop.bodyBound (witnessPrefix w i)
        (VerifierStrideCoordinates.skipped s b (reaction s hn i) x)
        (coefficient s b (reaction s hn i) x).bits (magnitude w i) (pos i) (neg i) ≤ B) :
    (machine b).HoareTime
      (fun inp work out => sourcePred (suffix s hn b x 0) inp ∧
        work = frame 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) (pos 0) (neg 0) ∧ OutAcc [] out)
      (fun inp work out => sourcePred (sourceSuffix s b (reaction s hn (s.reactions-1)) x) inp ∧
        work = frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode)
          (pos s.reactions) (neg s.reactions) ∧ OutAcc [] out)
      ((s.reactions-1)*(B+2)+(s.reactions-1+2)+1+
        finalCost s hn b x w (pos (s.reactions-1)) (neg (s.reactions-1))) := by
  have hl := VerifierCanonicalLoop.canonical_loop s hs hn b x w hw pos neg B
    (fun i hi => hpos i (by omega)) (fun i hi => hneg i (by omega)) hbound
  have hr : s.reactions-1 < w.flow.length := by rw [hw]; omega
  have he : s.reactions-1+1 = s.reactions := by omega
  have hk := witnessPrefix_length w (s.reactions-1) hr
  have hrv := VerifierCanonicalLoop.reaction_val s hn (s.reactions-1) (by omega)
  have hwp : Parked (wordTape w.encode) := VerifierReactionLoop.word_parked _
  have hfinal : (VerifierTraversalContribution.machine b).HoareTime
      (fun inp work out => sourcePred (suffix s hn b x (s.reactions-1)) inp ∧
        work = frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode)
          (pos (s.reactions-1)) (neg (s.reactions-1)) ∧ OutAcc [] out)
      (fun inp work out => sourcePred (sourceSuffix s b (reaction s hn (s.reactions-1)) x) inp ∧
        work = frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode)
          (pos s.reactions) (neg s.reactions) ∧ OutAcc [] out)
      (finalCost s hn b x w (pos (s.reactions-1)) (neg (s.reactions-1))) := by
    intro inp work out h
    have hi : (wordTape w.encode).HasBinarySuffix
        (BinaryFields.encode (witnessPrefix w (s.reactions-1)) ++
          (BinaryFields.encodeField (sign w (s.reactions-1) :: magnitude w (s.reactions-1)) ++
            witnessSuffix w (s.reactions-1))) := by
      unfold VerifierBufferedProduct.wordTape
      change ((Tape.init (w.encode.map Γ.ofBool)).move .right).HasBinarySuffix
        (BinaryFields.encode (witnessPrefix w (s.reactions-1)) ++
          (BinaryFields.encodeField (BinaryFields.writeInt (w.flow.getD (s.reactions-1) 0)) ++
            witnessSuffix w (s.reactions-1)))
      rw [← witness_split w (s.reactions-1) hr]
      exact (Tape.init_move_right_hasBinaryString w.encode).hasBinarySuffix
    have hc := VerifierTraversalContribution.contribution_hoare b (witnessPrefix w (s.reactions-1))
      (coefficient s b (reaction s hn (s.reactions-1)) x).bits (sign w (s.reactions-1))
      (magnitude w (s.reactions-1)) (pos (s.reactions-1)) (neg (s.reactions-1))
      (sourceSuffix s b (reaction s hn (s.reactions-1)) x) (witnessSuffix w (s.reactions-1))
      (wordTape w.encode) (VerifierIndexedField.counter (s.entities-1)) (regTape (s.reactions-1)) out hi
      ((Tape.StartInvariant.init_ofBool w.encode).move .right) rfl
      (VerifierReactionLoop.word_parked _).read_ne_start (parked_regTape _).read_ne_start
      h.2.2.parked.read_ne_start h.2.2.parked.1
    rw [hk,show 1+(s.reactions-1) = s.reactions from by omega] at hc
    obtain ⟨c,t,ht,hrun,hh,hin,hwc,hout⟩ := hc inp work out ⟨h.1,h.2.1,rfl⟩
    refine ⟨c,t,?_,hrun,hh,hin,?_,?_⟩
    · dsimp [finalCost,product]
      rw [hrv]
      omega
    · have hp := hpos (s.reactions-1) (by omega)
      have hn' := hneg (s.reactions-1) (by omega)
      rw [he] at hp hn'
      simpa only [frame,product,hrv,hp,hn'] using hwc
    · rw [hout]; exact h.2.2
  have hstable : ∀ inp work out,
      (sourcePred (suffix s hn b x (s.reactions-1)) inp ∧
        work = frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode)
          (pos (s.reactions-1)) (neg (s.reactions-1)) ∧ OutAcc [] out) →
      (sourcePred (suffix s hn b x (s.reactions-1)) (transitionInput inp) ∧
        (fun j => transitionTape (work j)) = frame s.reactions (s.entities-1) (s.reactions-1)
          (wordTape w.encode) (pos (s.reactions-1)) (neg (s.reactions-1)) ∧ OutAcc [] (transitionTape out)) := by
    intro inp work out h
    have hf : ∀ j, (work j).read ≠ .start := by
      intro j
      rw [h.2.1]
      exact (VerifierReactionLoop.frame_parked _ _ _ _ _ _ hwp j).read_ne_start
    obtain ⟨hi,hw',ho⟩ := phaseTransition_eq_self_of_reads_ne_start h.1.read_ne_start hf h.2.2.parked.read_ne_start
    simpa only [hi,hw',ho] using h
  exact seqTM_hoareTime _ _ hl hstable hfinal

end UnconstrainedPACDetection.VerifierCanonicalPhase

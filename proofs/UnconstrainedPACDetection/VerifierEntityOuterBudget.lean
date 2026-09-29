module

public import proofs.UnconstrainedPACDetection.VerifierEntityOuterLoop

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntityOuterBudget
open Complexity Complexity.TM
open VerifierCanonicalBuffers (envelope)
open VerifierEntityOuterLoop (iterationBound)

theorem bound (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (w : BinaryWitnessData.Witness) :
    s.entities*(iterationBound s w+2)+(s.entities+2) ≤
      20000*(s.encode.length+3*w.encode.length+2)^4 := by
  let K := s.encode.length+3*w.encode.length+2
  have hk : 1 ≤ K := by dsimp [K]; omega
  have hm : s.entities ≤ K := by
    have := VerifierEntitySum.entity_count s hs hn
    dsimp [K]; omega
  have hl : s.encode.length ≤ K := by dsimp [K]; omega
  have hk3 : K ≤ K^3 := by
    have hsquare : 1 ≤ K*K := by nlinarith
    calc
      K = K*1 := by omega
      _ ≤ K*(K*K) := Nat.mul_le_mul_left K hsquare
      _ = K^3 := by ring
  have hb : iterationBound s w+3 ≤ 18000*K^3 := by
    unfold iterationBound VerifierMaskedEntity.bodyBound envelope
    simp only [List.length_nil]
    change 17000*(K)^3+3*s.encode.length+2*s.entities+24+5*s.entities+19+3 ≤ _
    omega
  have hp := Nat.mul_le_mul hm hb
  have he : K*(18000*K^3) = 18000*K^4 := by ring
  rw [he] at hp
  have hpos : 1 ≤ K^4 := one_le_pow₀ hk
  change s.entities*(iterationBound s w+2)+(s.entities+2) ≤ 20000*K^4
  nlinarith only [hp,hpos]

theorem loop_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (hm : w.mask.length = s.entities) (initial : Bool) :
    VerifierEntityOuterLoop.machine.HoareTime
      (VerifierEntityLoopBody.pred s w 2 (regTape s.entities) initial)
      (VerifierEntityLoopBody.pred s w (2+s.entities) (regTape s.entities)
        (VerifierEntityOuterLoop.accumulator s hn w initial s.entities))
      (20000*(s.encode.length+3*w.encode.length+2)^4) :=
  (VerifierEntityOuterLoop.loop_hoare s hs hn w hw hm initial).mono_bound (bound s hs hn w)

end UnconstrainedPACDetection.VerifierEntityOuterBudget

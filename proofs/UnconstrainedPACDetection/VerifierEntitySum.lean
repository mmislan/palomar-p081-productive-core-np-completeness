module

public import proofs.UnconstrainedPACDetection.VerifierPhaseBoundary

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEntitySum
open Complexity Complexity.TM
open VerifierCanonicalBuffers (running envelope)
open VerifierCanonicalLoop (reaction suffix)
open VerifierCanonicalCoordinates (sourceSuffix coefficient)
open VerifierReactionLoop (frame sourcePred)
open VerifierBufferedProduct (wordTape)

def leftTotals (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions) (x : Fin s.entities)
    (w : BinaryWitnessData.Witness) (p₀ n₀ : List Bool) := running s hn false x w p₀ n₀ s.reactions

def bothTotals (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions) (x : Fin s.entities)
    (w : BinaryWitnessData.Witness) (p₀ n₀ : List Bool) :=
  running s hn true x w (leftTotals s hn x w p₀ n₀).1 (leftTotals s hn x w p₀ n₀).2 s.reactions

def machine : TM 11 := seqTM (VerifierCanonicalPhase.machine false)
  (seqTM VerifierPhaseBoundary.machine (VerifierCanonicalPhase.machine true))

theorem combined_budget (N M d : ℕ) (hm : M+1 ≤ 3*(N+1)) (hd : d ≤ 5*N+20) :
    250*(N+1)^3+d+250*(M+1)^3 ≤ 8000*(N+1)^3 := by
  have hp := Nat.pow_le_pow_left hm 3
  have hN : N+1 ≤ (N+1)^3 := by nlinarith [Nat.zero_le (N^2),Nat.zero_le (N^3)]
  nlinarith only [hp,hd,hN]

theorem entity_count (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) : s.entities ≤ s.encode.length := by
  have hc := VerifierEncodingBounds.count_le (s.values.map Nat.bits)
  have he := VerifierEncodingBounds.source_values_le s
  simp only [List.length_map] at hc
  change s.values.length = 2*(s.entities*s.reactions) at hs
  nlinarith

theorem entity_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (p₀ n₀ : List Bool) :
    machine.HoareTime
      (fun inp work out => sourcePred (suffix s hn false x 0) inp ∧
        work = frame 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) p₀ n₀ ∧ OutAcc [] out)
      (fun inp work out => sourcePred (sourceSuffix s true (reaction s hn (s.reactions-1)) x) inp ∧
        work = frame s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode)
          (bothTotals s hn x w p₀ n₀).1 (bothTotals s hn x w p₀ n₀).2 ∧ OutAcc [] out)
      (8000*(envelope s w p₀ n₀+1)^3) := by
  let p := (leftTotals s hn x w p₀ n₀).1
  let q := (leftTotals s hn x w p₀ n₀).2
  have hleft := VerifierSizedPhase.sized_phase s hs hn false x w hw p₀ n₀
  have hboundary := VerifierPhaseBoundary.boundary_hoare s hs hn x w p q
  have hright := VerifierSizedPhase.sized_phase s hs hn true x w hw p q
  have hwp := VerifierReactionLoop.word_parked w.encode
  have ht := seqTM_hoareTime _ _ hboundary
    (VerifierFlowReset.stable 1 (s.entities-1) (s.reactions-1) (wordTape w.encode)
      p q (suffix s hn true x 0) hwp) hright
  have hall := seqTM_hoareTime _ _ hleft
    (VerifierFlowReset.stable s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode)
      p q (sourceSuffix s false (reaction s hn (s.reactions-1)) x) hwp) ht
  have hbuf := VerifierCanonicalBuffers.buffer_bounds s hs hn false x w hw p₀ n₀ s.reactions le_rfl
  have he : envelope s w p q+1 ≤ 3*(envelope s w p₀ n₀+1) := by
    change p.length ≤ envelope s w p₀ n₀ ∧ q.length ≤ envelope s w p₀ n₀ at hbuf
    dsimp [envelope] at hbuf ⊢
    omega
  have hm := entity_count s hs hn
  have hn' := VerifierEncodingBounds.reaction_count w
  rw [hw] at hn'
  have hsmall : s.encode.length+2*(s.entities-1)+2*s.reactions+20 ≤
      5*(envelope s w p₀ n₀)+20 := by dsimp [envelope]; omega
  have hb := combined_budget (envelope s w p₀ n₀) (envelope s w p q)
    (s.encode.length+2*(s.entities-1)+2*s.reactions+20) he hsmall
  exact hall.mono_bound (by omega)

theorem net_value (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (x : Fin s.entities) (w : BinaryWitnessData.Witness) (p₀ n₀ : List Bool) :
    (BinaryFields.readNat (bothTotals s hn x w p₀ n₀).1 : ℤ)-
      BinaryFields.readNat (bothTotals s hn x w p₀ n₀).2 =
    (BinaryFields.readNat p₀ : ℤ)-BinaryFields.readNat n₀+
      ∑ j ∈ Finset.range s.reactions,
        ((coefficient s true (reaction s hn j) x : ℤ)-coefficient s false (reaction s hn j) x)*
          VerifierCanonicalContribution.flow w j := by
  have hl := VerifierSizedPhase.running_value s hn false x w p₀ n₀ s.reactions le_rfl
  have hr := VerifierSizedPhase.running_value s hn true x w
    (leftTotals s hn x w p₀ n₀).1 (leftTotals s hn x w p₀ n₀).2 s.reactions le_rfl
  change (BinaryFields.readNat (bothTotals s hn x w p₀ n₀).1 : ℤ)-
    BinaryFields.readNat (bothTotals s hn x w p₀ n₀).2 = _ at hr
  rw [hr]
  change (BinaryFields.readNat (leftTotals s hn x w p₀ n₀).1 : ℤ)-
    BinaryFields.readNat (leftTotals s hn x w p₀ n₀).2 = _ at hl
  rw [hl]
  simp only [Bool.false_eq_true,↓reduceIte,one_mul,neg_mul,
    sub_mul,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  ring

end UnconstrainedPACDetection.VerifierEntitySum

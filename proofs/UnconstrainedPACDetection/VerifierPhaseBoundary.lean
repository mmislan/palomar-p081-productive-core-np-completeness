module

public import proofs.UnconstrainedPACDetection.VerifierFlowReset

@[expose] public section

namespace UnconstrainedPACDetection.VerifierPhaseBoundary
open Complexity Complexity.TM
open VerifierFlowReset (pred)
open VerifierBufferedProduct (wordTape)
open VerifierCanonicalLoop (reaction suffix)
open VerifierCanonicalCoordinates (sourceSuffix)

theorem stride_hoare (k fuel : ℕ) (wit : Tape) (pos neg suffix : List Bool)
    (skipped : List (List Bool)) (hw : Parked wit) :
    VerifierSourceStride.machine.HoareTime
      (pred k skipped.length fuel wit pos neg (BinaryFields.encode skipped ++ suffix))
      (pred k skipped.length fuel wit pos neg suffix)
      ((BinaryFields.encode skipped).length+2*skipped.length+5) := by
  intro inp work out h
  have hs := VerifierReactionStep.stride_hoare k wit pos neg skipped suffix (regTape fuel) out
    hw.read_ne_start (parked_regTape _).read_ne_start h.2.2.parked.read_ne_start h.2.2.parked.1
  obtain ⟨c,t,ht,hr,hh,hi,hwork,hout⟩ := hs inp work out ⟨h.1,h.2.1,rfl⟩
  exact ⟨c,t,ht,hr,hh,hi,hwork,by rw [hout]; exact h.2.2⟩

def machine : TM 11 := seqTM VerifierSourceStride.machine VerifierFlowReset.machine

theorem boundary_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hn : 0 < s.reactions) (x : Fin s.entities) (w : BinaryWitnessData.Witness) (pos neg : List Bool) :
    machine.HoareTime
      (pred s.reactions (s.entities-1) (s.reactions-1) (wordTape w.encode) pos neg
        (sourceSuffix s false (reaction s hn (s.reactions-1)) x))
      (pred 1 (s.entities-1) (s.reactions-1) (wordTape w.encode) pos neg (suffix s hn true x 0))
      (s.encode.length+2*(s.entities-1)+2*s.reactions+18) := by
  let skipped := VerifierStrideCoordinates.skipped s false (reaction s hn (s.reactions-1)) x
  have hsuf := VerifierStrideCoordinates.source_side_boundary s hs
    (reaction s hn (s.reactions-1)) (reaction s hn 0) x
    (by rw [VerifierCanonicalLoop.reaction_val s hn (s.reactions-1) (by omega)]; omega)
    (VerifierCanonicalLoop.reaction_val s hn 0 hn)
  have hk : skipped.length = s.entities-1 := hsuf.1
  have he : sourceSuffix s false (reaction s hn (s.reactions-1)) x =
      BinaryFields.encode skipped ++ suffix s hn true x 0 := hsuf.2
  have hw := VerifierReactionLoop.word_parked w.encode
  have hstride := stride_hoare s.reactions (s.reactions-1) (wordTape w.encode) pos neg
    (suffix s hn true x 0) skipped hw
  rw [hk,← he] at hstride
  have hreset := VerifierFlowReset.reset_hoare s.reactions (s.entities-1) (s.reactions-1)
    (wordTape w.encode) pos neg (suffix s hn true x 0) hw rfl
  have h := seqTM_hoareTime _ _ hstride
    (VerifierFlowReset.stable s.reactions (s.entities-1) (s.reactions-1)
      (wordTape w.encode) pos neg (suffix s hn true x 0) hw) hreset
  have hb := VerifierEncodingBounds.skipped_le s false (reaction s hn (s.reactions-1)) x
  exact h.mono_bound (by change (BinaryFields.encode skipped).length ≤ s.encode.length at hb; omega)

end UnconstrainedPACDetection.VerifierPhaseBoundary

module

public import proofs.UnconstrainedPACDetection.VerifierPreparedCertificate
public import proofs.UnconstrainedPACDetection.BinaryIntegerVerifier

@[expose] public section

namespace UnconstrainedPACDetection.VerifierPreparedAcceptance
open Complexity Complexity.TM

theorem verdict_eq (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hm0 : 0 < s.entities) (hn : 0 < s.reactions) (w : BinaryWitnessData.Witness)
    (hm : w.mask.length = s.entities) (hw : w.flow.length = s.reactions) :
    VerifierEntityOuterLoop.accumulator s hn w (VerifierActivationNonempty.result s w) s.entities =
      BinaryIntegerVerifier.verify s.encode w.encode := by
  have hz : ¬(s.entities = 0 ∨ s.reactions = 0) := by omega
  simp only [BinaryIntegerVerifier.verify,BinarySourceData.decode_encode s hs,
    ite_eq_right hz,BinaryWitnessData.decode_encode]
  rw [ite_eq_left ⟨hm,hw,True.intro⟩]
  apply Bool.eq_iff_iff.mpr
  exact (VerifierPreparedCertificate.acceptance_iff s hn w hm).trans
    (checkIntegerFlow_iff s.toSource _ _).symm

/-- The existing prepared machine implements the already proved short-witness
verifier, without computing a redundant certificate magnitude bound. -/
theorem check_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (hm0 : 0 < s.entities) (hn : 0 < s.reactions) (w : BinaryWitnessData.Witness)
    (hm : w.mask.length = s.entities) (hw : w.flow.length = s.reactions) :
    VerifierPreparedCertificate.machine.HoareTime (VerifierPreparedCertificate.pre s w)
      (VerifierPreparedCertificate.prepared s w (2+s.entities)
        (BinaryIntegerVerifier.verify s.encode w.encode))
      (22000*(s.encode.length+3*w.encode.length+2)^4) := by
  rw [← verdict_eq s hs hm0 hn w hm hw]
  exact VerifierPreparedCertificate.check_hoare s hs hn w hm hw

end UnconstrainedPACDetection.VerifierPreparedAcceptance

module

public import proofs.UnconstrainedPACDetection.BinaryWitnessPolynomial
public import proofs.UnconstrainedPACDetection.BinaryWitnessData
public import proofs.UnconstrainedPACDetection.BoundedFlowChecker

@[expose] public section

/-! The total binary PAC verifier. This establishes language correctness;
polynomial machine execution is a separate, still-required theorem. -/

namespace UnconstrainedPACDetection.BinaryIntegerVerifier

def verify (input witness : List Bool) : Bool :=
  match BinarySourceData.decode input with
  | none => false
  | some s =>
      if s.entities = 0 ∨ s.reactions = 0 then false
      else match BinaryWitnessData.decode witness with
      | none => false
      | some w =>
          if w.mask.length = s.entities ∧ w.flow.length = s.reactions ∧ w.encode = witness then
            s.toSource.checkIntegerFlow (w.entities s.entities) (w.values s.reactions)
          else false

abbrev language := BinaryPACVerifier.language

theorem verify_sound {input witness : List Bool} (h : verify input witness = true) : input ∈ language := by
  unfold verify at h
  cases hs : BinarySourceData.decode input with
  | none => simp [hs] at h
  | some s =>
    simp only [hs] at h
    by_cases hempty : s.entities = 0 ∨ s.reactions = 0
    · simp [hempty] at h
    · rw [ite_eq_right hempty] at h
      cases hw : BinaryWitnessData.decode witness with
      | none => simp [hw] at h
      | some w =>
        simp only [hw] at h
        by_cases hshape : w.mask.length = s.entities ∧ w.flow.length = s.reactions ∧ w.encode = witness
        · rw [ite_eq_left hshape] at h
          exact ⟨s, hs, (exists_pac_iff_checkIntegerFlow s.toSource).2
            ⟨w.entities s.entities, w.values s.reactions, h⟩⟩
        · simp [hshape] at h

theorem bounded_accepts {input witness : List Bool}
    (h : BinaryPACVerifier.verify input witness = true) : verify input witness = true := by
  unfold BinaryPACVerifier.verify verify at *
  cases hs : BinarySourceData.decode input with
  | none => simp [hs] at h
  | some s =>
    simp only [hs] at *
    by_cases he : s.entities = 0 ∨ s.reactions = 0
    · simp [he] at h
    · rw [ite_eq_right he] at h ⊢
      cases hw : BinaryWitnessData.decode witness with
      | none => simp [hw] at h
      | some w =>
        simp only [hw] at *
        by_cases hk : w.mask.length = s.entities ∧ w.flow.length = s.reactions ∧ w.encode = witness
        · rw [ite_eq_left hk] at h ⊢
          have hh : s.toSource.checkIntegerFlow (w.entities s.entities) (w.values s.reactions) = true ∧
              ∀ r, ((w.values s.reactions) r).natAbs.size ≤
                ScaledInverseCertificate.flowBitBound s.reactions s.toSource.sideBitBound := by
            simpa [ReversibleSource.checkBoundedFlow] using h
          exact hh.1
        · simp [hk] at h

/-- A short certificate exists although this checker does not compute the
numerical flow bound. Machine execution and NP remain separate obligations. -/
theorem language_iff_short_verified (input : List Bool) :
    input ∈ language ↔ ∃ witness, witness.length ≤ 16 * (input.length + 1)^3 ∧
      verify input witness = true := by
  constructor
  · intro h
    obtain ⟨w, hw, hv⟩ := BinaryPACVerifier.exists_short_witness h
    exact ⟨w, hw, bounded_accepts hv⟩
  · rintro ⟨w, _, hv⟩
    exact verify_sound hv

end UnconstrainedPACDetection.BinaryIntegerVerifier

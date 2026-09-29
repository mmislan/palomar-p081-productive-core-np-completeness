module

public import proofs.UnconstrainedPACDetection.BinarySourceData
public import proofs.UnconstrainedPACDetection.BinaryWitnessData
public import proofs.UnconstrainedPACDetection.BoundedFlowChecker

@[expose] public section

/-! The total binary PAC verifier. This establishes language correctness;
polynomial machine execution is a separate, still-required theorem. -/

namespace UnconstrainedPACDetection.BinaryPACVerifier

def verify (input witness : List Bool) : Bool :=
  match BinarySourceData.decode input with
  | none => false
  | some s =>
      if s.entities = 0 ∨ s.reactions = 0 then false
      else match BinaryWitnessData.decode witness with
      | none => false
      | some w =>
          if w.mask.length = s.entities ∧ w.flow.length = s.reactions ∧ w.encode = witness then
            s.toSource.checkBoundedFlow (w.entities s.entities) (w.values s.reactions)
          else false

def language : Set (List Bool) :=
  {input | ∃ s, BinarySourceData.decode input = some s ∧ ∃ c, s.toSource.PAC c}

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
          exact ⟨s, hs, (exists_pac_iff_checkBoundedFlow s.toSource).2
            ⟨w.entities s.entities, w.values s.reactions, h⟩⟩
        · simp [hshape] at h

theorem verify_complete {input : List Bool} (h : input ∈ language) :
    ∃ witness, verify input witness = true := by
  obtain ⟨s, hs, hp⟩ := h
  have hm : s.entities ≠ 0 := by
    obtain ⟨c, hc⟩ := hp
    obtain ⟨x, _⟩ := hc.1.1
    have := x.isLt
    omega
  have hn : s.reactions ≠ 0 := by
    obtain ⟨c, hc⟩ := hp
    obtain ⟨r, _⟩ := hc.1.2.1
    have := r.isLt
    omega
  obtain ⟨X, flow, hcheck⟩ := (exists_pac_iff_checkBoundedFlow s.toSource).1 hp
  let w := BinaryWitnessData.fromCandidate X flow
  refine ⟨w.encode, ?_⟩
  simpa [verify, hs, hm, hn, w] using hcheck

theorem language_iff_verified (input : List Bool) :
    input ∈ language ↔ ∃ witness, verify input witness = true :=
  ⟨verify_complete, fun ⟨_, h⟩ => verify_sound h⟩

end UnconstrainedPACDetection.BinaryPACVerifier

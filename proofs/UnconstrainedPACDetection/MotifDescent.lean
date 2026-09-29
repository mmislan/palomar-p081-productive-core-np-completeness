module

public import proofs.UnconstrainedPACDetection.Motif
public import proofs.AutocatalyticCS.FiniteMinimality

@[expose] public section

namespace UnconstrainedPACDetection

variable {Entity Reaction : Type*}
  [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction]

theorem exists_pac_iff_exists_motif
    (source : ReversibleSource Entity Reaction) :
    (∃ candidate, source.PAC candidate) ↔
      ∃ candidate, source.Motif candidate := by
  constructor
  · rintro ⟨candidate, hcandidate⟩
    exact ⟨candidate, hcandidate.1⟩
  · rintro ⟨candidate, hcandidate⟩
    obtain ⟨core, _hcore_le, hcore⟩ :=
      AutocatalyticCS.exists_core_le source.Motif hcandidate
    exact ⟨core, hcore⟩

end UnconstrainedPACDetection

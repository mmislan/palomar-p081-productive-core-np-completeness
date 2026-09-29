module

public import proofs.UnconstrainedPACDetection.Motif

@[expose] public section

namespace UnconstrainedPACDetection

variable {Entity Reaction : Type*}
  [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]

noncomputable def ReversibleSource.fullAdmissible
    (source : ReversibleSource Entity Reaction) (entities : Finset Entity) :
    Finset Reaction := by
  classical
  exact Finset.univ.filter (source.sideAdmissible entities)

omit [Fintype Entity] [DecidableEq Reaction] in
theorem mem_fullAdmissible_iff
    (source : ReversibleSource Entity Reaction) (entities : Finset Entity)
    (reaction : Reaction) :
    reaction ∈ source.fullAdmissible entities ↔
      source.sideAdmissible entities reaction := by
  classical
  simp [ReversibleSource.fullAdmissible]

omit [Fintype Entity] [DecidableEq Entity] [DecidableEq Reaction] in
theorem productive_mono_reactions
    (source : ReversibleSource Entity Reaction)
    {entities : Finset Entity} {small large : Finset Reaction}
    (hsub : small ⊆ large) (hproductive : source.Productive entities small) :
    source.Productive entities large := by
  rcases hproductive with ⟨flow, hsupport, hpositive⟩
  refine ⟨flow, ?_, hpositive⟩
  intro reaction hnotmem
  exact hsupport reaction (fun hmem => hnotmem (hsub hmem))

omit [Fintype Entity] [DecidableEq Reaction] in
theorem exists_motif_with_entities_iff_fullAdmissible_productive
    (source : ReversibleSource Entity Reaction) (entities : Finset Entity) :
    (∃ reactions, source.Motif (entities, reactions)) ↔
      entities.Nonempty ∧
      (source.fullAdmissible entities).Nonempty ∧
      source.Productive entities (source.fullAdmissible entities) := by
  constructor
  · rintro ⟨reactions, hentities, hreactions, hadmissible, hproductive⟩
    have hsub : reactions ⊆ source.fullAdmissible entities := by
      intro reaction hreaction
      exact (mem_fullAdmissible_iff source entities reaction).2
        (hadmissible reaction hreaction)
    refine ⟨hentities, ?_, productive_mono_reactions source hsub hproductive⟩
    rcases hreactions with ⟨reaction, hreaction⟩
    exact ⟨reaction, hsub hreaction⟩
  · rintro ⟨hentities, hreactions, hproductive⟩
    refine ⟨source.fullAdmissible entities, hentities, hreactions, ?_, hproductive⟩
    intro reaction hreaction
    exact (mem_fullAdmissible_iff source entities reaction).1 hreaction

end UnconstrainedPACDetection

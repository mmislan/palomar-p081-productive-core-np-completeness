module

public import proofs.UnconstrainedPACDetection.MotifDescent

@[expose] public section

/-!
Transport of reversible sources and motifs across finite relabellings.

This is the first half of the embedded-witness adapter: a canonical
fork/return source can be relabelled onto the entity and reaction subtypes of
an ambient candidate without changing sides, net columns, or productivity.
-/

namespace UnconstrainedPACDetection

variable {Entity Reaction Entity' Reaction' : Type*}
  [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]
  [Fintype Entity'] [DecidableEq Entity']
  [Fintype Reaction'] [DecidableEq Reaction']

def ReversibleSource.reindex (source : ReversibleSource Entity Reaction)
    (entityEquiv : Entity' ≃ Entity) (reactionEquiv : Reaction' ≃ Reaction) :
    ReversibleSource Entity' Reaction' where
  left reaction entity := source.left (reactionEquiv reaction) (entityEquiv entity)
  right reaction entity := source.right (reactionEquiv reaction) (entityEquiv entity)

omit [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]
  [Fintype Entity'] [DecidableEq Entity']
  [Fintype Reaction'] [DecidableEq Reaction'] in
theorem ReversibleSource.reindex_net (source : ReversibleSource Entity Reaction)
    (entityEquiv : Entity' ≃ Entity) (reactionEquiv : Reaction' ≃ Reaction)
    (reaction : Reaction') (entity : Entity') :
    (source.reindex entityEquiv reactionEquiv).net reaction entity =
      source.net (reactionEquiv reaction) (entityEquiv entity) := by
  rfl

omit [Fintype Entity] [DecidableEq Reaction]
  [Fintype Entity'] [DecidableEq Reaction'] in
theorem ReversibleSource.Motif.of_reindex
    (source : ReversibleSource Entity Reaction)
    (entityEquiv : Entity' ≃ Entity) (reactionEquiv : Reaction' ≃ Reaction)
    (candidate : Candidate Entity' Reaction')
    (hmotif : (source.reindex entityEquiv reactionEquiv).Motif candidate) :
    source.Motif
      (candidate.1.map entityEquiv.toEmbedding,
        candidate.2.map reactionEquiv.toEmbedding) := by
  rcases hmotif with ⟨hentities, hreactions, hside, flow, hflowSupport, hpositive⟩
  refine ⟨Finset.map_nonempty.mpr hentities,
    Finset.map_nonempty.mpr hreactions, ?_, ?_⟩
  · intro reaction hreaction
    rw [Finset.mem_map] at hreaction
    obtain ⟨reaction', hreaction', rfl⟩ := hreaction
    rcases hside reaction' hreaction' with ⟨⟨leftEntity, hleftMem, hleft⟩,
      ⟨rightEntity, hrightMem, hright⟩⟩
    constructor
    · refine ⟨entityEquiv leftEntity, ?_, ?_⟩
      · exact Finset.mem_map.mpr ⟨leftEntity, hleftMem, rfl⟩
      · exact hleft
    · refine ⟨entityEquiv rightEntity, ?_, ?_⟩
      · exact Finset.mem_map.mpr ⟨rightEntity, hrightMem, rfl⟩
      · exact hright
  · let ambientFlow : Reaction → ℝ := fun reaction => flow (reactionEquiv.symm reaction)
    refine ⟨ambientFlow, ?_, ?_⟩
    · intro reaction hreaction
      apply hflowSupport (reactionEquiv.symm reaction)
      intro hmem
      apply hreaction
      exact Finset.mem_map.mpr ⟨reactionEquiv.symm reaction, hmem,
        reactionEquiv.apply_symm_apply reaction⟩
    · intro entity hentity
      rw [Finset.mem_map] at hentity
      obtain ⟨entity', hentity', rfl⟩ := hentity
      have hp := hpositive entity' hentity'
      let summand := fun reaction : Reaction =>
        source.net reaction (entityEquiv entity') * ambientFlow reaction
      have hreindex : Finset.univ.sum summand =
          Finset.univ.sum (fun reaction' : Reaction' =>
            summand (reactionEquiv reaction')) := by
        exact (Equiv.sum_comp reactionEquiv summand).symm
      change 0 < Finset.univ.sum summand
      rw [hreindex]
      simpa [summand, ambientFlow, ReversibleSource.reindex_net] using hp

omit [DecidableEq Reaction] [Fintype Entity'] [DecidableEq Reaction'] in
theorem exists_pac_of_reindex
    (source : ReversibleSource Entity Reaction)
    (entityEquiv : Entity' ≃ Entity) (reactionEquiv : Reaction' ≃ Reaction)
    (hexists : ∃ candidate,
      (source.reindex entityEquiv reactionEquiv).PAC candidate) :
    ∃ candidate, source.PAC candidate := by
  rw [exists_pac_iff_exists_motif]
  rcases hexists with ⟨candidate, hpac⟩
  exact ⟨(candidate.1.map entityEquiv.toEmbedding,
      candidate.2.map reactionEquiv.toEmbedding),
    hpac.1.of_reindex source entityEquiv reactionEquiv candidate⟩

def ReversibleSource.restrict (source : ReversibleSource Entity Reaction)
    (entities : Finset Entity) (reactions : Finset Reaction) :
    ReversibleSource (↥entities) (↥reactions) where
  left reaction entity := source.left reaction.1 entity.1
  right reaction entity := source.right reaction.1 entity.1

omit [Fintype Entity] in
theorem ReversibleSource.Motif.of_restrict
    (source : ReversibleSource Entity Reaction)
    (entities : Finset Entity) (reactions : Finset Reaction)
    (candidate : Candidate (↥entities) (↥reactions))
    (hmotif : (source.restrict entities reactions).Motif candidate) :
    source.Motif
      (candidate.1.map (Function.Embedding.subtype (fun x => x ∈ entities)),
        candidate.2.map (Function.Embedding.subtype (fun x => x ∈ reactions))) := by
  rcases hmotif with ⟨hentities, hreactions, hside, flow, hflowSupport, hpositive⟩
  refine ⟨Finset.map_nonempty.mpr hentities,
    Finset.map_nonempty.mpr hreactions, ?_, ?_⟩
  · intro reaction hreaction
    rw [Finset.mem_map] at hreaction
    obtain ⟨reaction', hreaction', rfl⟩ := hreaction
    rcases hside reaction' hreaction' with ⟨⟨leftEntity, hleftMem, hleft⟩,
      ⟨rightEntity, hrightMem, hright⟩⟩
    constructor
    · exact ⟨leftEntity.1,
        Finset.mem_map.mpr ⟨leftEntity, hleftMem, rfl⟩, hleft⟩
    · exact ⟨rightEntity.1,
        Finset.mem_map.mpr ⟨rightEntity, hrightMem, rfl⟩, hright⟩
  · let ambientFlow : Reaction → ℝ := fun reaction =>
      if hreaction : reaction ∈ reactions then flow ⟨reaction, hreaction⟩ else 0
    refine ⟨ambientFlow, ?_, ?_⟩
    · intro reaction hreaction
      by_cases hselected : reaction ∈ reactions
      · simp only [ambientFlow, hselected, dite_true]
        apply hflowSupport ⟨reaction, hselected⟩
        intro hmem
        apply hreaction
        exact Finset.mem_map.mpr ⟨⟨reaction, hselected⟩, hmem, rfl⟩
      · simp [ambientFlow, hselected]
    · intro entity hentity
      rw [Finset.mem_map] at hentity
      obtain ⟨entity', hentity', rfl⟩ := hentity
      have hp := hpositive entity' hentity'
      calc
        0 < reactions.sum (fun reaction =>
            source.net reaction entity'.1 * ambientFlow reaction) := by
          rw [← Finset.sum_finset_coe]
          simpa [ambientFlow, ReversibleSource.restrict, ReversibleSource.net] using hp
        _ = Finset.univ.sum (fun reaction =>
            source.net reaction entity'.1 * ambientFlow reaction) := by
          apply Finset.sum_subset (Finset.subset_univ reactions)
          intro reaction _ hnot
          simp [ambientFlow, hnot]

theorem exists_pac_of_restrict
    (source : ReversibleSource Entity Reaction)
    (entities : Finset Entity) (reactions : Finset Reaction)
    (hexists : ∃ candidate,
      (source.restrict entities reactions).PAC candidate) :
    ∃ candidate, source.PAC candidate := by
  rw [exists_pac_iff_exists_motif]
  rcases hexists with ⟨candidate, hpac⟩
  exact ⟨(candidate.1.map (Function.Embedding.subtype (fun x => x ∈ entities)),
      candidate.2.map (Function.Embedding.subtype (fun x => x ∈ reactions))),
    hpac.1.of_restrict source entities reactions candidate⟩

def embeddingRangeFinset {α β : Type*} [Fintype α] [DecidableEq β]
    (map : α ↪ β) : Finset β :=
  Finset.univ.map map

noncomputable def embeddingEquivRangeFinset
    {α β : Type*} [Fintype α] [DecidableEq β] (map : α ↪ β) :
    α ≃ ↥(embeddingRangeFinset map) :=
  (Equiv.ofInjective map map.injective).trans
    (Set.equivOfEq (by
      ext value
      simp [embeddingRangeFinset]))

omit [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]
  [Fintype Entity'] [DecidableEq Entity']
  [Fintype Reaction'] [DecidableEq Reaction'] in
@[simp] theorem embeddingEquivRangeFinset_apply
    {α β : Type*} [Fintype α] [DecidableEq β]
    (map : α ↪ β) (value : α) :
    (embeddingEquivRangeFinset map value).1 = map value := by
  rfl

def ReversibleSource.pullback (source : ReversibleSource Entity Reaction)
    (entityMap : Entity' ↪ Entity) (reactionMap : Reaction' ↪ Reaction) :
    ReversibleSource Entity' Reaction' where
  left reaction entity := source.left (reactionMap reaction) (entityMap entity)
  right reaction entity := source.right (reactionMap reaction) (entityMap entity)

omit [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]
  [Fintype Entity'] [DecidableEq Entity']
  [Fintype Reaction'] [DecidableEq Reaction'] in
@[simp] theorem ReversibleSource.pullback_left
    (source : ReversibleSource Entity Reaction)
    (entityMap : Entity' ↪ Entity) (reactionMap : Reaction' ↪ Reaction)
    (reaction : Reaction') (entity : Entity') :
    (source.pullback entityMap reactionMap).left reaction entity =
      source.left (reactionMap reaction) (entityMap entity) := by
  rfl

omit [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]
  [Fintype Entity'] [DecidableEq Entity']
  [Fintype Reaction'] [DecidableEq Reaction'] in
@[simp] theorem ReversibleSource.pullback_right
    (source : ReversibleSource Entity Reaction)
    (entityMap : Entity' ↪ Entity) (reactionMap : Reaction' ↪ Reaction)
    (reaction : Reaction') (entity : Entity') :
    (source.pullback entityMap reactionMap).right reaction entity =
      source.right (reactionMap reaction) (entityMap entity) := by
  rfl

omit [DecidableEq Reaction'] in
theorem exists_pac_of_pullback
    (source : ReversibleSource Entity Reaction)
    (entityMap : Entity' ↪ Entity) (reactionMap : Reaction' ↪ Reaction)
    (hexists : ∃ candidate,
      (source.pullback entityMap reactionMap).PAC candidate) :
    ∃ candidate, source.PAC candidate := by
  let entities := embeddingRangeFinset entityMap
  let reactions := embeddingRangeFinset reactionMap
  let entityEquiv := embeddingEquivRangeFinset entityMap
  let reactionEquiv := embeddingEquivRangeFinset reactionMap
  apply exists_pac_of_restrict source entities reactions
  apply exists_pac_of_reindex (source.restrict entities reactions)
    entityEquiv reactionEquiv
  simpa [entities, reactions, entityEquiv, reactionEquiv,
    ReversibleSource.reindex, ReversibleSource.restrict,
    ReversibleSource.pullback] using hexists

end UnconstrainedPACDetection

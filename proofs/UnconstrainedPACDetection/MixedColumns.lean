module

public import proofs.UnconstrainedPACDetection.Source

@[expose] public section

/-!
The nonambiguous literature model can be read directly from the signs of the
net stoichiometric matrix.  This is false with explicit catalysts, where an
entity may occur on both sides and cancel from the net column.
-/

namespace UnconstrainedPACDetection

variable {Entity Reaction : Type*}

def ReversibleSource.Nonambiguous (source : ReversibleSource Entity Reaction) : Prop :=
  ∀ reaction entity,
    source.left reaction entity = 0 ∨ source.right reaction entity = 0

theorem ReversibleSource.net_neg_iff_left_pos
    (source : ReversibleSource Entity Reaction) (hNA : source.Nonambiguous)
    (reaction : Reaction) (entity : Entity) :
    source.net reaction entity < 0 ↔ 0 < source.left reaction entity := by
  rcases hNA reaction entity with hleft | hright
  · simp [ReversibleSource.net, hleft]
  · simp [ReversibleSource.net, hright]

theorem ReversibleSource.net_pos_iff_right_pos
    (source : ReversibleSource Entity Reaction) (hNA : source.Nonambiguous)
    (reaction : Reaction) (entity : Entity) :
    0 < source.net reaction entity ↔ 0 < source.right reaction entity := by
  rcases hNA reaction entity with hleft | hright
  · simp [ReversibleSource.net, hleft]
  · simp [ReversibleSource.net, hright]

theorem ReversibleSource.sideAdmissible_iff_mixed
    [DecidableEq Entity] (source : ReversibleSource Entity Reaction)
    (hNA : source.Nonambiguous) (entities : Finset Entity) (reaction : Reaction) :
    source.sideAdmissible entities reaction ↔
      (∃ entity ∈ entities, source.net reaction entity < 0) ∧
        ∃ entity ∈ entities, 0 < source.net reaction entity := by
  simp only [ReversibleSource.sideAdmissible,
    source.net_neg_iff_left_pos hNA, source.net_pos_iff_right_pos hNA]

#print axioms UnconstrainedPACDetection.ReversibleSource.sideAdmissible_iff_mixed

end UnconstrainedPACDetection

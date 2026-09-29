module

public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod

@[expose] public section

/-!
Literal source semantics for unconstrained PAC detection.

A reversible reaction retains one identity and its two original nonnegative
integer complexes.  Its flux is signed; in particular, this is not a pair of
independently selectable irreversible reactions.
-/

namespace UnconstrainedPACDetection

structure ReversibleSource (Entity Reaction : Type*) where
  left : Reaction → Entity → ℕ
  right : Reaction → Entity → ℕ

variable {Entity Reaction : Type*}

variable {Entity Reaction : Type*}
def ReversibleSource.net (source : ReversibleSource Entity Reaction)
    (reaction : Reaction) (entity : Entity) : ℝ :=
  (source.right reaction entity : ℝ) - (source.left reaction entity : ℝ)

def ReversibleSource.sideAdmissible [DecidableEq Entity]
    (source : ReversibleSource Entity Reaction) (entities : Finset Entity)
    (reaction : Reaction) : Prop :=
  (∃ entity ∈ entities, 0 < source.left reaction entity) ∧
    ∃ entity ∈ entities, 0 < source.right reaction entity

variable [Fintype Entity] [DecidableEq Entity] [Fintype Reaction] [DecidableEq Reaction]
abbrev Candidate (Entity Reaction : Type*) := Finset Entity × Finset Reaction

def ReversibleSource.Productive (source : ReversibleSource Entity Reaction)
    (entities : Finset Entity) (reactions : Finset Reaction) : Prop :=
  ∃ flow : Reaction → ℝ,
    (∀ reaction, reaction ∉ reactions → flow reaction = 0) ∧
    ∀ entity ∈ entities,
      0 < Finset.univ.sum (fun reaction =>
        source.net reaction entity * flow reaction)

def ReversibleSource.Motif (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) : Prop :=
  candidate.1.Nonempty ∧
    candidate.2.Nonempty ∧
    (∀ reaction ∈ candidate.2,
      source.sideAdmissible candidate.1 reaction) ∧
    source.Productive candidate.1 candidate.2

def ReversibleSource.PAC (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) : Prop :=
  source.Motif candidate ∧
    ∀ ⦃smaller⦄, smaller < candidate → ¬ source.Motif smaller

end UnconstrainedPACDetection

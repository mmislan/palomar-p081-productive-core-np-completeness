module

public import proofs.RAF.Core.RAF

@[expose] public section

namespace MinRAFApprox

universe u v w

/-- A finite SET COVER instance with the promise that its universe is covered. -/
structure SetCoverInstance (U : Type u) (J : Type v)
    [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J] where
  sets : J → Finset U
  coverable : ∀ u : U, ∃ j : J, u ∈ sets j

namespace SetCoverInstance

variable {U : Type u} {J : Type v}
  [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J]

def Covers (I : SetCoverInstance U J) (C : Finset J) : Prop :=
  ∀ u : U, ∃ j ∈ C, u ∈ I.sets j

theorem univ_covers (I : SetCoverInstance U J) : I.Covers Finset.univ := by
  intro u
  obtain ⟨j, hj⟩ := I.coverable u
  exact ⟨j, Finset.mem_univ j, hj⟩

end SetCoverInstance

/-- Abstract reaction names of the amplified source: one gate per universe
element and one reaction per `(set, block-coordinate)` pair. -/
inductive Reaction (U : Type u) (J : Type v) (K : Type w)
  | gate (u : U)
  | block (j : J) (k : K)
  deriving DecidableEq, Fintype

open Reaction
section
variable {U : Type u} {J : Type v} {K : Type w} [Fintype U] [DecidableEq U] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

noncomputable def canonicalRAF (C : Finset J) : Finset (Reaction U J K) := by
  classical
  exact Finset.univ.filter fun r =>
    match r with
    | gate _ => True
    | block j _ => j ∈ C
end


end MinRAFApprox

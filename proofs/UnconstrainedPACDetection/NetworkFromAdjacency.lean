module

public import proofs.UnconstrainedPACDetection.SimplePathsToNetwork

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

deriving instance DecidableEq, Fintype for PhysicalVertex

namespace FromAdjacency

variable {V : Type*}

@[reducible] def Arcs (A : PhysicalVertex V → PhysicalVertex V → Prop) :=
  {e : (Bool ⊕ V) × (Bool ⊕ V) //
    A (tailVertex e.1) (headVertex e.2) ∧ tailVertex e.1 ≠ headVertex e.2}

instance [DecidableEq V] (A : PhysicalVertex V → PhysicalVertex V → Prop) :
    DecidableEq (Arcs A) := by unfold Arcs; infer_instance

instance [Fintype V] [DecidableEq V]
    (A : PhysicalVertex V → PhysicalVertex V → Prop) [DecidableRel A] :
    Fintype (Arcs A) := by unfold Arcs; infer_instance

def network (A : PhysicalVertex V → PhysicalVertex V → Prop) : Network V (Arcs A) where
  tail e := e.1.1
  head e := e.1.2
  noLoop e v ht hh := e.2.2 (by rw [ht, hh]; rfl)

theorem adjacency_iff (A : PhysicalVertex V → PhysicalVertex V → Prop)
    (u v : PhysicalVertex V) : adjacency (network A) u v ↔
    DirectedPathNormalization.pruned A (.source false) (.source true)
      (.sink false) (.sink true) u v := by
  constructor
  · rintro ⟨e, rfl, rfl⟩
    refine ⟨e.2.1, e.2.2, ?_, ?_, ?_, ?_⟩
    · exact tailVertex_ne_sink _ _
    · exact tailVertex_ne_sink _ _
    · exact headVertex_ne_source _ _
    · exact headVertex_ne_source _ _
  · rintro ⟨ha, hne, ht0, ht1, hs0, hs1⟩
    cases u with
    | source b =>
      cases v with
      | source c => cases c <;> contradiction
      | sink c => exact ⟨⟨(Sum.inl b, Sum.inl c), ha, hne⟩, rfl, rfl⟩
      | internal z => exact ⟨⟨(Sum.inl b, Sum.inr z), ha, hne⟩, rfl, rfl⟩
    | sink b => cases b <;> contradiction
    | internal z =>
      cases v with
      | source c => cases c <;> contradiction
      | sink c => exact ⟨⟨(Sum.inr z, Sum.inl c), ha, hne⟩, rfl, rfl⟩
      | internal w => exact ⟨⟨(Sum.inr z, Sum.inr w), ha, hne⟩, rfl, rfl⟩

theorem pac_iff_unrestricted_linkage [Fintype V] [DecidableEq V]
    (A : PhysicalVertex V → PhysicalVertex V → Prop) [DecidableRel A] :
    (∃ candidate, (source (network A)).PAC candidate) ↔
      DirectedPathNormalization.Linkage A (.source false) (.source true)
        (.sink false) (.sink true) := by
  classical
  have he : adjacency (network A) = DirectedPathNormalization.pruned A
      (.source false) (.source true) (.sink false) (.sink true) := by
    funext u v
    exact propext (adjacency_iff A u v)
  rw [pac_iff_simple_linkage, he]
  exact DirectedPathNormalization.linkage_pruned_iff A _ _ _ _

end FromAdjacency
end UnconstrainedPACDetection.DirectedLinkageSource

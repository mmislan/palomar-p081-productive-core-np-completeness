module

public import proofs.UnconstrainedPACDetection.NetworkFromAdjacency
public import proofs.UnconstrainedPACDetection.DirectedPathRelabeling

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource.MarkedGraph

variable {X : Type*}

def Internal (T : (Bool ⊕ Bool) ↪ X) := {x : X // x ∉ Set.range T}

instance [DecidableEq X] (T : (Bool ⊕ Bool) ↪ X) : DecidableEq (Internal T) := by
  unfold Internal
  infer_instance

noncomputable instance [Fintype X] (T : (Bool ⊕ Bool) ↪ X) : Fintype (Internal T) := by
  classical
  unfold Internal
  infer_instance

def decode (T : (Bool ⊕ Bool) ↪ X) : PhysicalVertex (Internal T) → X
  | .source b => T (Sum.inl b)
  | .sink b => T (Sum.inr b)
  | .internal x => x.1

theorem decode_injective (T : (Bool ⊕ Bool) ↪ X) : Function.Injective (decode T) := by
  intro u v h
  cases u <;> cases v
  · rename_i a b
    exact congrArg PhysicalVertex.source (Sum.inl.inj (T.injective h))
  · cases T.injective h
  · rename_i a b
    exact False.elim (b.2 ⟨Sum.inl a, h⟩)
  · cases T.injective h
  · rename_i a b
    exact congrArg PhysicalVertex.sink (Sum.inr.inj (T.injective h))
  · rename_i a b
    exact False.elim (b.2 ⟨Sum.inr a, h⟩)
  · rename_i a b
    exact False.elim (a.2 ⟨Sum.inl b, h.symm⟩)
  · rename_i a b
    exact False.elim (a.2 ⟨Sum.inr b, h.symm⟩)
  · exact congrArg PhysicalVertex.internal (Subtype.ext h)

theorem decode_surjective (T : (Bool ⊕ Bool) ↪ X) : Function.Surjective (decode T) := by
  classical
  intro x
  by_cases hx : x ∈ Set.range T
  · obtain ⟨b, hb⟩ := hx
    cases b with
    | inl b => exact ⟨.source b, hb⟩
    | inr b => exact ⟨.sink b, hb⟩
  · exact ⟨.internal ⟨x, hx⟩, rfl⟩

noncomputable def vertexEquiv (T : (Bool ⊕ Bool) ↪ X) : PhysicalVertex (Internal T) ≃ X :=
  Equiv.ofBijective (decode T) ⟨decode_injective T, decode_surjective T⟩

def pulled (A : X → X → Prop) (T : (Bool ⊕ Bool) ↪ X)
    (u v : PhysicalVertex (Internal T)) : Prop := A (decode T u) (decode T v)

instance (A : X → X → Prop) [DecidableRel A] (T : (Bool ⊕ Bool) ↪ X) :
    DecidableRel (pulled A T) := fun _ _ => inferInstanceAs (Decidable (A _ _))

def graphSource [DecidableEq X] (A : X → X → Prop) (T : (Bool ⊕ Bool) ↪ X) :=
  source (FromAdjacency.network (pulled A T))

/-- Full semantic normalization from arbitrary finite graphs with four
distinct marked terminals to the actual literal PAC source. Polynomial
encoding and the hard-source complexity theorem are separate obligations. -/
theorem pac_iff_marked_linkage [Fintype X] [DecidableEq X]
    (A : X → X → Prop) [DecidableRel A] (T : (Bool ⊕ Bool) ↪ X) :
    (∃ candidate, (graphSource A T).PAC candidate) ↔
      DirectedPathNormalization.Linkage A (T (Sum.inl false)) (T (Sum.inl true))
        (T (Sum.inr false)) (T (Sum.inr true)) := by
  classical
  unfold graphSource
  rw [FromAdjacency.pac_iff_unrestricted_linkage]
  exact DirectedPathNormalization.linkage_pull_iff (vertexEquiv T) A
    (.source false) (.source true) (.sink false) (.sink true)

end UnconstrainedPACDetection.DirectedLinkageSource.MarkedGraph

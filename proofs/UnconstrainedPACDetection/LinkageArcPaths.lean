module

public import proofs.UnconstrainedPACDetection.LinkageEndpointEquivs
public import proofs.UnconstrainedPACDetection.BoundaryFirstReturn

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

/-- Original arc identities, with sources and sinks interpreted as distinct
physical terminal classes. The tail list contains the source and all internal
vertices; the last head is a sink and belongs to neither class. -/
structure ArcPath {V E : Type*} (D : Network V E) (s t : Bool) where
  length : ℕ
  positive : 0 < length
  arcs : Fin length → E
  start : D.tail (arcs ⟨0, positive⟩) = Sum.inl s
  finish : D.head (arcs ⟨length - 1, by omega⟩) = Sum.inl t
  consecutive : ∀ i (hi : i + 1 < length),
    D.head (arcs ⟨i, by omega⟩) = D.tail (arcs ⟨i + 1, hi⟩)
  internal : ∀ i : Fin length, 0 < i.1 → ∃ v, D.tail (arcs i) = Sum.inr v
  tail_injective : Function.Injective (fun i => D.tail (arcs i))

namespace EndpointEquivs

variable {V E : Type*} {D : Network V E} {rs : Finset (Bool ⊕ V)}

def next (Q : EndpointEquivs D rs) : Equiv.Perm rs := Q.tail.symm.trans Q.head

def boundary (rs : Finset (Bool ⊕ V)) : Set rs := {x | ∃ b, x.1 = Sum.inl b}

noncomputable def returnArcs (Q : EndpointEquivs D rs) (a : boundary rs) :
    Fin (BoundaryFirstReturn.length Q.next (boundary rs) a) → E :=
  fun i => Q.tail.symm ((Q.next : rs → rs)^[i.1] a.1)

theorem returnArcs_tail (Q : EndpointEquivs D rs) (a : boundary rs)
    (i : Fin (BoundaryFirstReturn.length Q.next (boundary rs) a)) :
    D.tail (Q.returnArcs a i) = ((Q.next : rs → rs)^[i.1] a.1).1 := by
  rw [← Q.tail_val]
  simp [returnArcs]

theorem returnArcs_head (Q : EndpointEquivs D rs) (a : boundary rs)
    (i : Fin (BoundaryFirstReturn.length Q.next (boundary rs) a)) :
    D.head (Q.returnArcs a i) = ((Q.next : rs → rs)^[i.1 + 1] a.1).1 := by
  rw [← Q.head_val, Function.iterate_succ_apply']
  rfl

noncomputable def returnPath (Q : EndpointEquivs D rs) (a : boundary rs)
    (s t : Bool) (hs : a.1.1 = Sum.inl s)
    (ht : ((Q.next : rs → rs)^[BoundaryFirstReturn.length Q.next (boundary rs) a]
      a.1).1 = Sum.inl t) : ArcPath D s t := by
  classical
  let n := BoundaryFirstReturn.length Q.next (boundary rs) a
  have hn : 0 < n := (BoundaryFirstReturn.length_spec Q.next (boundary rs) a).1
  refine ⟨n, hn, Q.returnArcs a, ?_, ?_, ?_, ?_, ?_⟩
  · rw [returnArcs_tail]
    exact hs
  · rw [returnArcs_head]
    change ((Q.next : rs → rs)^[n - 1 + 1] a.1).1 = Sum.inl t
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
    exact ht
  · intro i hi
    rw [returnArcs_head, returnArcs_tail]
  · intro i hi
    rw [returnArcs_tail]
    have hnot := BoundaryFirstReturn.no_internal_boundary Q.next (boundary rs) a hi i.2
    cases hx : ((Q.next : rs → rs)^[i.1] a.1).1 with
    | inl b => exact False.elim (hnot ⟨b, hx⟩)
    | inr v => exact ⟨v, rfl⟩
  · intro i j hij
    apply BoundaryFirstReturn.prefix_injective Q.next (boundary rs) a
    apply Subtype.ext
    simpa only [returnArcs_tail] using hij

theorem returnPaths_disjoint (Q : EndpointEquivs D rs) (a b : boundary rs)
    (hab : a ≠ b) (s t u v : Bool) (hs ht hu hv)
    (i : Fin (Q.returnPath a s t hs ht).length)
    (j : Fin (Q.returnPath b u v hu hv).length) :
    D.tail ((Q.returnPath a s t hs ht).arcs i) ≠
      D.tail ((Q.returnPath b u v hu hv).arcs j) := by
  let ia : Fin (BoundaryFirstReturn.length Q.next (boundary rs) a) :=
    ⟨i.1, by simpa [returnPath] using i.2⟩
  let jb : Fin (BoundaryFirstReturn.length Q.next (boundary rs) b) :=
    ⟨j.1, by simpa [returnPath] using j.2⟩
  have hdis : D.tail (Q.returnArcs a ia) ≠ D.tail (Q.returnArcs b jb) := by
    rw [returnArcs_tail, returnArcs_tail]
    intro h
    exact BoundaryFirstReturn.prefixes_disjoint Q.next (boundary rs) a b hab ia.2 jb.2
      (Subtype.ext h)
  have hai : (Q.returnPath a s t hs ht).arcs i = Q.returnArcs a ia := by
    unfold returnPath
    congr 1
  have hbj : (Q.returnPath b u v hu hv).arcs j = Q.returnArcs b jb := by
    unfold returnPath
    congr 1
  rw [hai, hbj]
  exact hdis

theorem two_arc_paths (Q : EndpointEquivs D rs)
    (hbound : ∀ b : Bool, Sum.inl b ∈ rs) :
    ∃ t u : Bool, t ≠ u ∧ ∃ (P : ArcPath D false t) (R : ArcPath D true u),
      ∀ i j, D.tail (P.arcs i) ≠ D.tail (R.arcs j) := by
  classical
  let a : boundary rs := ⟨⟨Sum.inl false, hbound false⟩, false, rfl⟩
  let b : boundary rs := ⟨⟨Sum.inl true, hbound true⟩, true, rfl⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg (fun x : boundary rs => x.1.1) h
    simp [a, b] at this
  obtain ⟨t, ht⟩ := (BoundaryFirstReturn.length_spec Q.next (boundary rs) a).2
  obtain ⟨u, hu⟩ := (BoundaryFirstReturn.length_spec Q.next (boundary rs) b).2
  have htu : t ≠ u := by
    intro h
    apply hab
    apply BoundaryFirstReturn.destinations_injective Q.next (boundary rs)
    apply Subtype.ext
    exact ht.trans ((congrArg Sum.inl h).trans hu.symm)
  refine ⟨t, u, htu, Q.returnPath a false t rfl ht,
    Q.returnPath b true u rfl hu, ?_⟩
  exact Q.returnPaths_disjoint a b hab false t true u rfl ht rfl hu

end EndpointEquivs
end UnconstrainedPACDetection.DirectedLinkageSource

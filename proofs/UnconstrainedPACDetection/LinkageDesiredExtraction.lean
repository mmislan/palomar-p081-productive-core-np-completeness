module

public import proofs.UnconstrainedPACDetection.LinkagePhysicalPaths
public import proofs.UnconstrainedPACDetection.LinkageCrossedKernel

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

/-- Any nonempty closed mixed independent selection yields the prescribed
same-label two-linkage, not merely an unspecified pairing of the terminals. -/
theorem independent_selection_linkage
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (D : Network V E) (rs : Finset (Bool ⊕ V)) (hne : rs.Nonempty)
    (hrow : ∀ r ∈ rs, (Finset.univ.filter (fun e => matrix D r e ≠ 0)).card ≤ 2)
    (hmixed : ∀ r ∈ rs, (∃ e, matrix D r e < 0) ∧ ∃ e, 0 < matrix D r e)
    (hcol : ∀ e, (rs.filter (fun r => matrix D r e ≠ 0)).card = 2)
    (hind : LinearIndependent ℝ (fun r : rs => fun e : E => (matrix D r.1 e : ℝ))) :
    ∃ (P : ArcPath D false false) (R : ArcPath D true true),
      Disjoint P.vertices R.vertices := by
  classical
  have hs := independent_has_source D rs hne hrow hmixed hcol hind
  have ht := (terminal_mem_iff D rs hrow hmixed hcol).mp hs
  let Q := endpointEquivs D rs hrow hmixed hcol hs
  let a : EndpointEquivs.boundary rs := ⟨⟨Sum.inl false, hs⟩, false, rfl⟩
  let b : EndpointEquivs.boundary rs := ⟨⟨Sum.inl true, ht⟩, true, rfl⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg (fun x : EndpointEquivs.boundary rs => x.1.1) h
    simp [a, b] at hv
  obtain ⟨t, hta⟩ := (BoundaryFirstReturn.length_spec Q.next (EndpointEquivs.boundary rs) a).2
  obtain ⟨u, hub⟩ := (BoundaryFirstReturn.length_spec Q.next (EndpointEquivs.boundary rs) b).2
  have htu : t ≠ u := by
    intro h
    apply hab
    apply BoundaryFirstReturn.destinations_injective Q.next (EndpointEquivs.boundary rs)
    apply Subtype.ext
    exact hta.trans ((congrArg Sum.inl h).trans hub.symm)
  have htf : t = false := by
    cases t
    · rfl
    · have huf : u = false := by cases u <;> simp_all
      subst u
      have hra : (Q.next : rs → rs)^[BoundaryFirstReturn.length Q.next
          (EndpointEquivs.boundary rs) a] a.1 = b.1 := Subtype.ext hta
      have hrb : (Q.next : rs → rs)^[BoundaryFirstReturn.length Q.next
          (EndpointEquivs.boundary rs) b] b.1 = a.1 := Subtype.ext hub
      exact False.elim (Q.crossed_selection_dependent a b rfl rfl hra hrb
        (endpoints_mem_of_column_degree D rs hcol) hind)
  subst t
  have hut : u = true := by cases u <;> simp_all
  subst u
  let P := Q.returnPath a false false rfl hta
  let R := Q.returnPath b true true rfl hub
  refine ⟨P, R, P.physical_disjoint R Bool.false_ne_true ?_⟩
  exact Q.returnPaths_disjoint a b hab false false true true rfl hta rfl hub

end UnconstrainedPACDetection.DirectedLinkageSource

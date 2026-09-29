module

public import proofs.UnconstrainedPACDetection.LinkageTerminalCoverage

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

noncomputable def equivOfUniqueFibers {E X : Type*} (f : E → X)
    (hf : ∀ x, ∃! e, f e = x) : E ≃ X :=
  Equiv.ofBijective f ⟨by
    intro e d hed
    obtain ⟨a, _, hu⟩ := hf (f e)
    exact (hu e rfl).trans (hu d hed.symm).symm,
    fun x => (hf x).exists⟩

/-- The original tail/head labels become bijections with the selected label
type. Boolean labels denote sources on the tail side and sinks on the head side. -/
structure EndpointEquivs {V E : Type*} (D : Network V E)
    (rs : Finset (Bool ⊕ V)) where
  tail : E ≃ rs
  head : E ≃ rs
  tail_val : ∀ e, (tail e).1 = D.tail e
  head_val : ∀ e, (head e).1 = D.head e

noncomputable def endpointEquivs {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (D : Network V E) (rs : Finset (Bool ⊕ V))
    (hrow : ∀ r ∈ rs, (Finset.univ.filter (fun e => matrix D r e ≠ 0)).card ≤ 2)
    (hmixed : ∀ r ∈ rs, (∃ e, matrix D r e < 0) ∧ ∃ e, 0 < matrix D r e)
    (hcol : ∀ e, (rs.filter (fun r => matrix D r e ≠ 0)).card = 2)
    (hs : Sum.inl false ∈ rs) : EndpointEquivs D rs := by
  classical
  have ht : Sum.inl true ∈ rs := (terminal_mem_iff D rs hrow hmixed hcol).mp hs
  have hclosed := endpoints_mem_of_column_degree D rs hcol
  have htailmem : ∀ e, D.tail e ∈ rs := by
    intro e
    cases he : D.tail e with
    | inl b => cases b <;> assumption
    | inr v => simpa [he, tailRow] using (hclosed e).1
  have hheadmem : ∀ e, D.head e ∈ rs := by
    intro e
    cases he : D.head e with
    | inl b => cases b <;> assumption
    | inr v => simpa [he, headRow] using (hclosed e).2
  have htu : ∀ x : rs, ∃! e, D.tail e = x.1 := by
    intro x
    rcases x with ⟨x, hx⟩
    cases x with
    | inl b =>
      obtain ⟨h0, h1⟩ := source_unique_arcs D (hrow _ hs) (hmixed _ hs)
      cases b <;> assumption
    | inr v => exact (internal_unique_arcs D v (hrow _ hx) (hmixed _ hx)).1
  have hhu : ∀ x : rs, ∃! e, D.head e = x.1 := by
    intro x
    rcases x with ⟨x, hx⟩
    cases x with
    | inl b =>
      obtain ⟨h0, h1⟩ := sink_unique_arcs D (hrow _ ht) (hmixed _ ht)
      cases b <;> assumption
    | inr v => exact (internal_unique_arcs D v (hrow _ hx) (hmixed _ hx)).2
  let tf : E → rs := fun e => ⟨D.tail e, htailmem e⟩
  let hf : E → rs := fun e => ⟨D.head e, hheadmem e⟩
  have htf : ∀ x, ∃! e, tf e = x := by
    intro x
    exact (existsUnique_congr (fun e =>
      (show D.tail e = x.1 ↔ tf e = x from
        ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩))).mp (htu x)
  have hhf : ∀ x, ∃! e, hf e = x := by
    intro x
    exact (existsUnique_congr (fun e =>
      (show D.head e = x.1 ↔ hf e = x from
        ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩))).mp (hhu x)
  exact ⟨equivOfUniqueFibers tf htf, equivOfUniqueFibers hf hhf,
    fun _ => rfl, fun _ => rfl⟩

theorem endpoint_equivs_exist {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (D : Network V E) (rs : Finset (Bool ⊕ V))
    (hrow : ∀ r ∈ rs, (Finset.univ.filter (fun e => matrix D r e ≠ 0)).card ≤ 2)
    (hmixed : ∀ r ∈ rs, (∃ e, matrix D r e < 0) ∧ ∃ e, 0 < matrix D r e)
    (hcol : ∀ e, (rs.filter (fun r => matrix D r e ≠ 0)).card = 2)
    (hs : Sum.inl false ∈ rs) : Nonempty (EndpointEquivs D rs) :=
  ⟨endpointEquivs D rs hrow hmixed hcol hs⟩

end UnconstrainedPACDetection.DirectedLinkageSource

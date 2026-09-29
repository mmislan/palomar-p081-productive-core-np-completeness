module

public import proofs.UnconstrainedPACDetection.LinkageSelectedDegrees

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

theorem unique_fiber_card {E : Type*} [Fintype E] (p : E → Prop)
    [DecidablePred p] (h : ∃! e, p e) :
    (Finset.univ.filter p).card = 1 := by
  classical
  obtain ⟨e, he, hu⟩ := h
  apply Finset.card_eq_one.mpr
  refine ⟨e, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨hu x, fun hx => hx ▸ he⟩

/-- The two-incidence equality supplies endpoint closure in the original
network, not just in the selected matrix. -/
theorem endpoints_mem_of_column_degree {V E : Type*} [Fintype V] [DecidableEq V]
    (D : Network V E) (rs : Finset (Bool ⊕ V))
    (hcol : ∀ e, (rs.filter (fun r => matrix D r e ≠ 0)).card = 2) :
    ∀ e, tailRow (D.tail e) ∈ rs ∧ headRow (D.head e) ∈ rs := by
  intro e
  have hm := DegreeTwoSaturation.no_incidence_outside rs
    (fun r => matrix D r e ≠ 0) (le_of_eq (column_degree_two D e)) (hcol e)
  exact ⟨hm _ ((matrix_ne_zero_iff D _ e).mpr (Or.inl rfl)),
    hm _ ((matrix_ne_zero_iff D _ e).mpr (Or.inr rfl))⟩

/-- Closed mixed degree-two selections use both terminal rows or neither.
No connectivity or independence assumption is needed for this counting step. -/
theorem terminal_mem_iff {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (D : Network V E) (rs : Finset (Bool ⊕ V))
    (hrow : ∀ r ∈ rs, (Finset.univ.filter (fun e => matrix D r e ≠ 0)).card ≤ 2)
    (hmixed : ∀ r ∈ rs, (∃ e, matrix D r e < 0) ∧ ∃ e, 0 < matrix D r e)
    (hcol : ∀ e, (rs.filter (fun r => matrix D r e ≠ 0)).card = 2) :
    Sum.inl false ∈ rs ↔ Sum.inl true ∈ rs := by
  classical
  have hclosed := endpoints_mem_of_column_degree D rs hcol
  have hinternal : ∀ v,
      (Finset.univ.filter (fun e => D.tail e = Sum.inr v)).card =
        (Finset.univ.filter (fun e => D.head e = Sum.inr v)).card := by
    intro v
    by_cases hv : Sum.inr v ∈ rs
    · obtain ⟨ht, hh⟩ := internal_unique_arcs D v (hrow _ hv) (hmixed _ hv)
      rw [unique_fiber_card _ ht, unique_fiber_card _ hh]
    · have ht : (Finset.univ.filter (fun e => D.tail e = Sum.inr v)).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro e _ he
        exact hv (by simpa [he, tailRow] using (hclosed e).1)
      have hh : (Finset.univ.filter (fun e => D.head e = Sum.inr v)).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro e _ he
        exact hv (by simpa [he, headRow] using (hclosed e).2)
      rw [ht, hh]
  have hsource : ∀ b : Bool,
      (Finset.univ.filter (fun e => D.tail e = Sum.inl b)).card =
        if Sum.inl false ∈ rs then 1 else 0 := by
    intro b
    by_cases hs : Sum.inl false ∈ rs
    · rw [ite_eq_left hs]
      obtain ⟨h0, h1⟩ := source_unique_arcs D (hrow _ hs) (hmixed _ hs)
      cases b
      · exact unique_fiber_card _ h0
      · exact unique_fiber_card _ h1
    · rw [ite_eq_right hs]
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro e _ he
      exact hs (by simpa [he, tailRow] using (hclosed e).1)
  have hsink : ∀ b : Bool,
      (Finset.univ.filter (fun e => D.head e = Sum.inl b)).card =
        if Sum.inl true ∈ rs then 1 else 0 := by
    intro b
    by_cases hs : Sum.inl true ∈ rs
    · rw [ite_eq_left hs]
      obtain ⟨h0, h1⟩ := sink_unique_arcs D (hrow _ hs) (hmixed _ hs)
      cases b
      · exact unique_fiber_card _ h0
      · exact unique_fiber_card _ h1
    · rw [ite_eq_right hs]
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro e _ he
      exact hs (by simpa [he, headRow] using (hclosed e).2)
  have ht : Fintype.card E =
      ∑ x : Bool ⊕ V, (Finset.univ.filter (fun e => D.tail e = x)).card := by
    simpa only [Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
        (f := D.tail) (by intro e _; exact Finset.mem_univ _))
  have hh : Fintype.card E =
      ∑ x : Bool ⊕ V, (Finset.univ.filter (fun e => D.head e = x)).card := by
    simpa only [Finset.card_univ] using
      (Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
        (f := D.head) (by intro e _; exact Finset.mem_univ _))
  have hi : (∑ v : V, (Finset.univ.filter (fun e => D.tail e = Sum.inr v)).card) =
      ∑ v : V, (Finset.univ.filter (fun e => D.head e = Sum.inr v)).card :=
    Finset.sum_congr rfl (fun v _ => hinternal v)
  simp only [Fintype.sum_sum_type, hsource, hsink, Finset.sum_const,
    Fintype.card_bool, Finset.card_univ, smul_eq_mul] at ht hh
  by_cases hs : Sum.inl false ∈ rs <;> by_cases hk : Sum.inl true ∈ rs <;>
    simp_all

end UnconstrainedPACDetection.DirectedLinkageSource

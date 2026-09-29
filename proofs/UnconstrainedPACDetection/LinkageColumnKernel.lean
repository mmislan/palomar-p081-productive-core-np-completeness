module

public import proofs.UnconstrainedPACDetection.LinkageTerminalCoverage

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

theorem matrix_two_terms {V E : Type*} [DecidableEq V] (D : Network V E)
    (r : Bool ⊕ V) (e : E) :
    matrix D r e = (if r = tailRow (D.tail e) then tailSign (D.tail e) else 0) +
      (if r = headRow (D.head e) then
        headSign (D.head e) * factor (D.tail e) * factor (D.head e) else 0) := by
  have hne := rows_distinct D e
  by_cases ht : r = tailRow (D.tail e)
  · subst r
    simp [matrix, hne]
  · simp [matrix, ht]

/-- Each selected column's row-dependence equation has exactly its two
physical endpoint terms. No determinant expansion or connectivity is assumed. -/
theorem weighted_column_sum {V E : Type*} [DecidableEq V] (D : Network V E)
    (rs : Finset (Bool ⊕ V)) (x : Bool ⊕ V → ℝ) (e : E)
    (ht : tailRow (D.tail e) ∈ rs) (hh : headRow (D.head e) ∈ rs) :
    (∑ r ∈ rs, x r * (matrix D r e : ℝ)) =
      x (tailRow (D.tail e)) * (tailSign (D.tail e) : ℝ) +
      x (headRow (D.head e)) *
        ((headSign (D.head e) * factor (D.tail e) * factor (D.head e) : ℤ) : ℝ) := by
  simp_rw [matrix_two_terms, Int.cast_add, mul_add, Finset.sum_add_distrib]
  simp [mul_ite, ht, hh]

theorem internal_column_sum_zero {V E : Type*} [DecidableEq V] (D : Network V E)
    (rs : Finset (Bool ⊕ V)) (e : E)
    (hclosed : tailRow (D.tail e) ∈ rs ∧ headRow (D.head e) ∈ rs)
    (hs : Sum.inl false ∉ rs) (ht : Sum.inl true ∉ rs) :
    (∑ r ∈ rs, (matrix D r e : ℝ)) = 0 := by
  have hsum := weighted_column_sum D rs (fun _ => 1) e hclosed.1 hclosed.2
  cases he : D.tail e with
  | inl b => exact False.elim (hs (by simpa [he, tailRow] using hclosed.1))
  | inr v =>
    cases hf : D.head e with
    | inl b => exact False.elim (ht (by simpa [hf, headRow] using hclosed.2))
    | inr w => simpa [he, hf, tailSign, headSign, factor] using hsum

/-- A nonempty independent closed mixed selection must contain both terminal
rows: otherwise its constant row combination is zero. -/
theorem independent_has_source {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (D : Network V E) (rs : Finset (Bool ⊕ V)) (hne : rs.Nonempty)
    (hrow : ∀ r ∈ rs, (Finset.univ.filter (fun e => matrix D r e ≠ 0)).card ≤ 2)
    (hmixed : ∀ r ∈ rs, (∃ e, matrix D r e < 0) ∧ ∃ e, 0 < matrix D r e)
    (hcol : ∀ e, (rs.filter (fun r => matrix D r e ≠ 0)).card = 2)
    (hind : LinearIndependent ℝ (fun r : rs => fun e : E => (matrix D r.1 e : ℝ))) :
    Sum.inl false ∈ rs := by
  classical
  by_contra hs
  have ht : Sum.inl true ∉ rs := fun ht =>
    hs ((terminal_mem_iff D rs hrow hmixed hcol).mpr ht)
  have hc := endpoints_mem_of_column_degree D rs hcol
  have hz : (∑ r : rs, (1 : ℝ) • (fun e : E => (matrix D r.1 e : ℝ))) = 0 := by
    ext e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, one_mul, Pi.zero_apply]
    rw [Finset.sum_coe_sort rs (fun r => (matrix D r e : ℝ))]
    exact internal_column_sum_zero D rs e (hc e) hs ht
  obtain ⟨r, hr⟩ := hne
  have hbad := (Fintype.linearIndependent_iff.mp hind) (fun _ => 1) hz ⟨r, hr⟩
  norm_num at hbad

end UnconstrainedPACDetection.DirectedLinkageSource

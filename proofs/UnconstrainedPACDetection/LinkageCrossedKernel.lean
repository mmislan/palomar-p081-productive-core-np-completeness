module

public import proofs.UnconstrainedPACDetection.LinkageArcPaths
public import proofs.UnconstrainedPACDetection.LinkageColumnKernel
public import proofs.UnconstrainedPACDetection.BoundaryPotential

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

def crossedRowWeight {V : Type*} (c : Bool ⊕ V → ℝ) : Bool ⊕ V → ℝ
  | Sum.inl false => 2
  | Sum.inl true => 1
  | Sum.inr v => c (Sum.inr v)

theorem crossed_endpoint_equation {V E : Type*} (D : Network V E)
    (c : Bool ⊕ V → ℝ) (h0 : c (Sum.inl false) = 2)
    (h1 : c (Sum.inl true) = -1) (e : E)
    (hi : ∀ v, D.head e = Sum.inr v → c (D.head e) = c (D.tail e))
    (hs0 : D.head e = Sum.inl false → c (D.tail e) = -1)
    (hs1 : D.head e = Sum.inl true → c (D.tail e) = 2) :
    crossedRowWeight c (tailRow (D.tail e)) * (tailSign (D.tail e) : ℝ) +
      crossedRowWeight c (headRow (D.head e)) *
        ((headSign (D.head e) * factor (D.tail e) * factor (D.head e) : ℤ) : ℝ) = 0 := by
  cases ht : D.tail e with
  | inl b =>
    cases hh : D.head e with
    | inl d => cases b <;> cases d <;>
        simp_all [crossedRowWeight, tailRow, headRow, tailSign, headSign, factor]
               norm_num at *
    | inr v => cases b <;>
        simp_all [crossedRowWeight, tailRow, headRow, tailSign, headSign, factor]
  | inr v =>
    cases hh : D.head e with
    | inl d => cases d <;>
        simp_all [crossedRowWeight, tailRow, headRow, tailSign, headSign, factor]
    | inr w =>
        simp_all [crossedRowWeight, tailRow, headRow, tailSign, headSign, factor]

namespace EndpointEquivs

/-- Crossed first returns give a nonzero dependence on the entire selected
matrix, including columns in unused internal cycles. -/
theorem crossed_selection_dependent {V E : Type*} [DecidableEq V]
    {D : Network V E} {rs : Finset (Bool ⊕ V)}
    (Q : EndpointEquivs D rs) (a b : boundary rs)
    (ha : a.1.1 = Sum.inl false) (hb : b.1.1 = Sum.inl true)
    (hra : (Q.next : rs → rs)^[BoundaryFirstReturn.length Q.next (boundary rs) a] a.1 = b.1)
    (hrb : (Q.next : rs → rs)^[BoundaryFirstReturn.length Q.next (boundary rs) b] b.1 = a.1)
    (hclosed : ∀ e, tailRow (D.tail e) ∈ rs ∧ headRow (D.head e) ∈ rs) :
    ¬ LinearIndependent ℝ (fun r : rs => fun e : E => (matrix D r.1 e : ℝ)) := by
  classical
  have hab : a ≠ b := by
    intro h
    have hv := congrArg (fun z : boundary rs => z.1.1) h
    change a.1.1 = b.1.1 at hv
    rw [ha, hb] at hv
    cases hv
  obtain ⟨c, hc0, hc1, hcstep, hcp0, hcp1, _⟩ :=
    BoundaryFirstReturn.crossed_potential_exists Q.next (boundary rs) a b hab hra hrb 2 (-1)
  let d : Bool ⊕ V → ℝ := fun r => if h : r ∈ rs then c ⟨r, h⟩ else 0
  have hd (r : rs) : d r.1 = c r := by simp [d]
  have hd0 : d (Sum.inl false) = 2 := by rw [← ha, hd]; exact hc0
  have hd1 : d (Sum.inl true) = -1 := by rw [← hb, hd]; exact hc1
  have hdt (e : E) : d (D.tail e) = c (Q.tail e) := by rw [← Q.tail_val, hd]
  have hdh (e : E) : d (D.head e) = c (Q.head e) := by rw [← Q.head_val, hd]
  have hnext (e : E) : Q.next (Q.tail e) = Q.head e := by simp [next]
  have heq (e : E) :
      crossedRowWeight d (tailRow (D.tail e)) * (tailSign (D.tail e) : ℝ) +
        crossedRowWeight d (headRow (D.head e)) *
          ((headSign (D.head e) * factor (D.tail e) * factor (D.head e) : ℤ) : ℝ) = 0 := by
    apply crossed_endpoint_equation D d hd0 hd1 e
    · intro v hv
      rw [hdt, hdh]
      have hn : Q.next (Q.tail e) ∉ boundary rs := by
        rintro ⟨j, hj⟩
        rw [hnext, Q.head_val, hv] at hj
        cases hj
      simpa only [hnext] using hcstep (Q.tail e) hn
    · intro hv
      rw [hdt]
      apply hcp0
      rw [hnext]
      apply Subtype.ext
      exact (Q.head_val e).trans (hv.trans ha.symm)
    · intro hv
      rw [hdt]
      apply hcp1
      rw [hnext]
      apply Subtype.ext
      exact (Q.head_val e).trans (hv.trans hb.symm)
  intro hind
  have hz : (∑ r : rs, crossedRowWeight d r.1 •
      (fun e : E => (matrix D r.1 e : ℝ))) = 0 := by
    ext e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [Finset.sum_coe_sort rs (fun r => crossedRowWeight d r * (matrix D r e : ℝ))]
    rw [weighted_column_sum D rs (crossedRowWeight d) e (hclosed e).1 (hclosed e).2]
    exact heq e
  have hbad := (Fintype.linearIndependent_iff.mp hind)
    (fun r => crossedRowWeight d r.1) hz a.1
  norm_num [ha, crossedRowWeight] at hbad

end EndpointEquivs
end UnconstrainedPACDetection.DirectedLinkageSource

module

public import proofs.UnconstrainedPACDetection.DirectedLinkageSource

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

/-- The integer signs retain the original directed incidence and all four
terminal labels, despite merging terminal reaction rows. -/
theorem local_signs {V E : Type*} [DecidableEq V]
    (D : Network V E) (e : E) (v : V) :
    ((matrix D (Sum.inr v) e < 0 ↔ D.tail e = Sum.inr v) ∧
      (0 < matrix D (Sum.inr v) e ↔ D.head e = Sum.inr v)) ∧
    ((matrix D (Sum.inl false) e < 0 ↔ D.tail e = Sum.inl false) ∧
      (0 < matrix D (Sum.inl false) e ↔ D.tail e = Sum.inl true)) ∧
    ((matrix D (Sum.inl true) e < 0 ↔ D.head e = Sum.inl false) ∧
      (0 < matrix D (Sum.inl true) e ↔ D.head e = Sum.inl true)) := by
  rcases ht : D.tail e with a | u <;> rcases hh : D.head e with b | w
  · cases a <;> cases b <;>
      simp [matrix, ht, hh, tailRow, headRow, tailSign, headSign, factor]
  · cases a <;> by_cases hv : v = w <;>
      simp_all [matrix, tailRow, headRow, tailSign, headSign, factor] <;> aesop
  · cases b <;> by_cases hv : v = u <;>
      simp_all [matrix, tailRow, headRow, tailSign, headSign, factor] <;> aesop
  · have huw : u ≠ w := by
      intro h
      subst w
      exact D.noLoop e u ht hh
    by_cases hvu : v = u <;> by_cases hvw : v = w <;>
      simp_all [matrix, tailRow, headRow, tailSign, headSign, factor] <;> aesop

/-- Terminal labels are retained even when the network has no internal vertex. -/
theorem terminal_signs {V E : Type*} [DecidableEq V]
    (D : Network V E) (e : E) :
    ((matrix D (Sum.inl false) e < 0 ↔ D.tail e = Sum.inl false) ∧
      (0 < matrix D (Sum.inl false) e ↔ D.tail e = Sum.inl true)) ∧
    ((matrix D (Sum.inl true) e < 0 ↔ D.head e = Sum.inl false) ∧
      (0 < matrix D (Sum.inl true) e ↔ D.head e = Sum.inl true)) := by
  rcases ht : D.tail e with a | u <;> rcases hh : D.head e with b | w
  · cases a <;> cases b <;>
      simp [matrix, ht, hh, tailRow, headRow, tailSign, headSign, factor]
  · cases a <;> simp [matrix, ht, hh, tailRow, headRow, tailSign]
  · cases b <;> simp [matrix, ht, hh, tailRow, headRow, headSign, factor]
  · simp [matrix, ht, hh, tailRow, headRow]

end UnconstrainedPACDetection.DirectedLinkageSource

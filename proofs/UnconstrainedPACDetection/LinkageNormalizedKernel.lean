module

public import proofs.UnconstrainedPACDetection.LinkageColumnKernel

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

noncomputable def tailPotential {V : Type*} (x : Bool ⊕ V → ℝ) : Bool ⊕ V → ℝ
  | Sum.inl false => x (Sum.inl false)
  | Sum.inl true => -x (Sum.inl false) / 2
  | Sum.inr v => x (Sum.inr v)

def headPotential {V : Type*} (x : Bool ⊕ V → ℝ) : Bool ⊕ V → ℝ
  | Sum.inl false => -x (Sum.inl true)
  | Sum.inl true => 2 * x (Sum.inl true)
  | Sum.inr v => x (Sum.inr v)

theorem normalized_endpoint_equation {V E : Type*} (D : Network V E)
    (x : Bool ⊕ V → ℝ) (e : E)
    (h : x (tailRow (D.tail e)) * (tailSign (D.tail e) : ℝ) +
      x (headRow (D.head e)) *
        ((headSign (D.head e) * factor (D.tail e) * factor (D.head e) : ℤ) : ℝ) = 0) :
    headPotential x (D.head e) = tailPotential x (D.tail e) := by
  cases ht : D.tail e with
  | inl b =>
    cases hh : D.head e with
    | inl d => cases b <;> cases d <;>
        simp_all [tailPotential, headPotential, tailRow, headRow, tailSign, headSign, factor] <;> linarith
    | inr v => cases b <;>
        simp_all [tailPotential, headPotential, tailRow, headRow, tailSign, headSign, factor] <;> linarith
  | inr v =>
    cases hh : D.head e with
    | inl d => cases d <;>
        simp_all [tailPotential, headPotential, tailRow, headRow, tailSign, headSign, factor] <;> linarith
    | inr w =>
        simp_all [tailPotential, headPotential, tailRow, headRow, tailSign, headSign, factor]
        linarith

end UnconstrainedPACDetection.DirectedLinkageSource

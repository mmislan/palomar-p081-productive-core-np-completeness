module

public import proofs.UnconstrainedPACDetection.FormulaOutdegree
public import proofs.UnconstrainedPACDetection.FormulaSourceArcCount

@[expose] public section

namespace UnconstrainedPACDetection.FormulaDegreeSum
open Complexity.SAT FormulaWiring FormulaOutdegree

def externalEquiv (φ : CNF) : External φ ≃
    Fin (varCount φ+1) ⊕ ((Fin (varCount φ) × Bool × Fin (levels φ+1)) ⊕ Fin (φ.length+1)) where
  toFun
    | .var v => .inl v
    | .rail v b j => .inr (.inl (v,b,j))
    | .clause c => .inr (.inr c)
  invFun
    | .inl v => .var v
    | .inr (.inl (v,b,j)) => .rail v b j
    | .inr (.inr c) => .clause c
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with v | ⟨v,b,j⟩ | c <;> rfl

theorem adjacency_card (φ : CNF) :
    Fintype.card {e : Vertex φ × Vertex φ // adjacency φ e.1 e.2} =
      ∑ x : Vertex φ, degree φ x := by
  let e : {e : Vertex φ × Vertex φ // adjacency φ e.1 e.2} ≃
      (Σ x : Vertex φ, {y : Vertex φ // adjacency φ x y}) :=
    { toFun := fun e => ⟨e.val.1,⟨e.val.2,e.property⟩⟩
      invFun := fun e => ⟨(e.1,e.2.val),e.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa [Fintype.card_sigma,degree] using Fintype.card_congr e

theorem external_sum (φ : CNF) (f : External φ → Nat) :
    (∑ x, f x) = (∑ v : Fin (varCount φ+1), f (.var v)) +
      ((∑ v : Fin (varCount φ), ∑ b : Bool, ∑ j : Fin (levels φ+1), f (.rail v b j)) +
      ∑ c : Fin (φ.length+1), f (.clause c)) := by
  have he := Fintype.sum_equiv (externalEquiv φ) f
    (fun x => f ((externalEquiv φ).symm x)) (by intro x; simp)
  rw [he]
  simp [Fintype.sum_sum_type,Fintype.sum_prod_type,externalEquiv]

/-- Partition the actual source header by the four disjoint vertex constructors. -/
theorem table_entities_decomposed (φ : CNF) :
    (FormulaPACEncoding.table φ).entities =
      (∑ i : Fin (levels φ), ∑ a : ControlSwitch.V, degree φ (SwitchStack.sw i a)) +
      (∑ v : Fin (varCount φ+1), degree φ (.inr (.var v))) +
      2 * varCount φ * (levels φ+1) +
      ∑ c : Fin (φ.length+1), degree φ (.inr (.clause c)) := by
  rw [FormulaSourceArcCount.table_entities,adjacency_card]
  change (∑ x : (Fin (levels φ) × ControlSwitch.V) ⊕ External φ, degree φ x) = _
  have hs : (∑ x : (Fin (levels φ) × ControlSwitch.V) ⊕ External φ, degree φ x) =
      (∑ z : Fin (levels φ) × ControlSwitch.V, degree φ (.inl z)) +
      ∑ x : External φ, degree φ (.inr x) := Fintype.sum_sum_type _
  rw [hs]
  rw [Fintype.sum_prod_type,external_sum]
  rw [rail_total]
  simp only [SwitchStack.sw]
  omega

end UnconstrainedPACDetection.FormulaDegreeSum

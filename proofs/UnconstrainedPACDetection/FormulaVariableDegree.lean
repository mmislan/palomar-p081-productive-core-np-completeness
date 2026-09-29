module

public import proofs.UnconstrainedPACDetection.FormulaDegreeSum

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVariableDegree
open Complexity.SAT FormulaWiring SwitchStack FormulaOutdegree

theorem variable_iff (φ : CNF) (v : Fin (varCount φ+1)) (hv : v.val < varCount φ)
    (y : Vertex φ) : adjacency φ (.inr (.var v)) y ↔
      y = .inr (.rail ⟨v.val,hv⟩ false 0) ∨ y = .inr (.rail ⟨v.val,hv⟩ true 0) := by
  cases y with
  | inl y => obtain ⟨i,a⟩ := y; simp [adjacency,Edge,DataWire,sw]
  | inr y =>
    cases y with
    | var w => simp [adjacency,Edge,DataWire]
    | rail w b j =>
      change (v.val = w.val ∧ j.val = 0) ↔ _
      constructor
      · rintro ⟨hw,hj⟩
        have hw' : w = ⟨v.val,hv⟩ := Fin.ext hw.symm
        have hj' : j = 0 := Fin.ext (by simpa using hj)
        subst w
        subst j
        cases b <;> simp
      · rintro (he | he) <;> cases he <;> simp
    | clause c => simp [adjacency,Edge,DataWire]; omega

theorem variable_last_iff (φ : CNF) (y : Vertex φ) :
    adjacency φ (.inr (.var (Fin.last (varCount φ)))) y ↔ y = .inr (.clause 0) := by
  cases y with
  | inl y => obtain ⟨i,a⟩ := y; simp [adjacency,Edge,DataWire,sw]
  | inr y =>
    cases y with
    | var w => simp [adjacency,Edge,DataWire]
    | clause c => simp [adjacency,Edge,DataWire]
    | rail w b j =>
      have hw := w.isLt
      simp [adjacency,Edge,DataWire]
      omega

theorem variable_degree (φ : CNF) (v : Fin (varCount φ+1)) (hv : v.val < varCount φ) :
    degree φ (.inr (.var v)) = 2 := by
  unfold degree
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (variable_iff φ v hv))]
  exact Fintype.card_subtype_eq_or_eq_of_ne (by simp)

theorem variable_last_degree (φ : CNF) :
    degree φ (.inr (.var (Fin.last (varCount φ)))) = 1 := by
  unfold degree
  have he := Fintype.card_congr (Equiv.subtypeEquivRight (variable_last_iff φ))
  simpa using he

theorem variable_total (φ : CNF) :
    (∑ v : Fin (varCount φ+1), degree φ (.inr (.var v))) = 2 * varCount φ + 1 := by
  rw [Fin.sum_univ_castSucc,variable_last_degree]
  have he (v : Fin (varCount φ)) : degree φ (.inr (.var v.castSucc)) = 2 :=
    variable_degree φ v.castSucc v.isLt
  simp_rw [he]
  simp [Nat.mul_comm]

theorem table_after_rails_variables (φ : CNF) :
    (FormulaPACEncoding.table φ).entities =
      (∑ i : Fin (levels φ), ∑ a : ControlSwitch.V, degree φ (sw i a)) +
      (2 * varCount φ + 1) + 2 * varCount φ * (levels φ+1) +
      ∑ c : Fin (φ.length+1), degree φ (.inr (.clause c)) := by
  rw [FormulaDegreeSum.table_entities_decomposed,variable_total]

end UnconstrainedPACDetection.FormulaVariableDegree

module

public import proofs.UnconstrainedPACDetection.FormulaBlockingCardinality
public import proofs.UnconstrainedPACDetection.DirectedPathNormalization

@[expose] public section

namespace UnconstrainedPACDetection.FormulaNormalization
open Complexity.SAT FormulaWiring SwitchStack ControlSwitch

private theorem next_not_self (a : V) : a ∉ next a := by
  fin_cases a <;> decide

private theorem next_not_zero (a : V) : (0 : V) ∉ next a := by
  fin_cases a <;> decide

private theorem next_not_one (a : V) : (1 : V) ∉ next a := by
  fin_cases a <;> decide

theorem no_loop (φ : CNF) (x : Vertex φ) : ¬adjacency φ x x := by
  cases x with
  | inl x =>
    obtain ⟨i,a⟩ := x
    simp [adjacency,Edge,DataWire,sw,next_not_self]
  | inr x =>
    cases x with
    | var v => simp [adjacency,Edge,DataWire]
    | clause c => simp [adjacency,Edge,DataWire]
    | rail v b j => simp [adjacency,Edge,DataWire]

theorem no_into_sourceP (φ : CNF) (x : Vertex φ) : ¬adjacency φ x (sourceP φ) := by
  cases x with
  | inl x =>
    obtain ⟨i,a⟩ := x
    simp [adjacency,Edge,sourceP,sw,next_not_one]
  | inr x => simp [adjacency,Edge,sourceP,sw]

theorem no_into_sourceQ (φ : CNF) (x : Vertex φ) : ¬adjacency φ x (sourceQ φ) := by
  cases x with
  | inl x =>
    obtain ⟨i,a⟩ := x
    have hi := i.isLt
    have hp := levels_pos φ
    simp [adjacency,Edge,sourceQ,sw,next_not_zero]
    omega
  | inr x => simp [adjacency,Edge,sourceQ,sw]

theorem no_from_sinkQ (φ : CNF) (x : Vertex φ) : ¬adjacency φ (sinkQ φ) x := by
  cases x with
  | inl x =>
    obtain ⟨i,a⟩ := x
    simp [adjacency,Edge,sinkQ,sw,next,edges]
  | inr x => simp [adjacency,Edge,sinkQ,sw]

theorem no_from_sinkP (φ : CNF) (x : Vertex φ) : ¬adjacency φ (sinkP φ) x := by
  cases x with
  | inl x =>
    obtain ⟨i,a⟩ := x
    simp only [adjacency,Edge,sinkP,sw,DataWire]
    rintro ⟨_,_,l,hl⟩
    obtain ⟨cl,hcl,_⟩ := ClauseSatisfaction.lookup_clause φ i hl
    simp at hcl
  | inr x => cases x <;> simp [adjacency,Edge,sinkP,DataWire]

/-- The source adapter's graph normalization deletes no formula arc. -/
theorem pruned_eq (φ : CNF) :
    DirectedPathNormalization.pruned (adjacency φ) (sourceP φ) (sourceQ φ)
      (sinkP φ) (sinkQ φ) = adjacency φ := by
  funext x y
  apply propext
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h,?_,?_,?_,?_,?_⟩
    · rintro rfl; exact no_loop φ x h
    · rintro rfl; exact no_from_sinkP φ y h
    · rintro rfl; exact no_from_sinkQ φ y h
    · rintro rfl; exact no_into_sourceP φ x h
    · rintro rfl; exact no_into_sourceQ φ x h

end UnconstrainedPACDetection.FormulaNormalization

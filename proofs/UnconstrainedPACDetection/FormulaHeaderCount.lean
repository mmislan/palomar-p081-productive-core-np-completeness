module

public import proofs.UnconstrainedPACDetection.FormulaSwitchDegree

@[expose] public section

namespace UnconstrainedPACDetection.FormulaHeaderCount
open Complexity.SAT FormulaWiring SwitchStack ControlSwitch FormulaOutdegree FormulaSwitchDegree

private theorem internal_four : internalDegree 4 = 0 := by decide
private theorem internal_five : internalDegree 5 = 0 := by decide
private theorem internal_six : internalDegree 6 = 0 := by decide
private theorem internal_seven : internalDegree 7 = 0 := by decide

theorem switch_degree_formula (φ : CNF) (i : Fin (levels φ)) (a : V) :
    degree φ (sw i a) = internalDegree a +
      (if a = 4 then (if 0 < i.val then 1 else 0) else 0) +
      (if a = 5 then 1 else 0) +
      (if a = 6 then (if (lookup φ i).isSome then 1 else 0) else 0) +
      (if a = 7 then (if (lookup φ i).isSome then 1 else 0) else 0) := by
  by_cases h4 : a = 4
  · subst a; simp [port4_degree,internal_four]
  by_cases h5 : a = 5
  · subst a; simp [port5_degree,internal_five]
  by_cases h6 : a = 6
  · subst a; simp [port6_degree,internal_six]
  by_cases h7 : a = 7
  · subst a; simp [port7_degree,internal_seven]
  simp [h4,h5,h6,h7,ordinary_degree φ i a h4 h5 h6 h7]

theorem switch_level_total (φ : CNF) (i : Fin (levels φ)) :
    (∑ a : V, degree φ (sw i a)) = 30 +
      (if 0 < i.val then 1 else 0) + 2 * (if (lookup φ i).isSome then 1 else 0) := by
  simp_rw [switch_degree_formula,Finset.sum_add_distrib]
  rw [internal_total]
  simp
  split_ifs <;> omega

theorem predecessor_total (φ : CNF) :
    (∑ i : Fin (levels φ), if 0 < i.val then 1 else 0) = (occurrences φ).length := by
  change (∑ i : Fin ((occurrences φ).length+1), if 0 < i.val then 1 else 0) = _
  rw [Fin.sum_univ_succ]
  simp

theorem real_lookup_total (φ : CNF) :
    (∑ i : Fin (levels φ), if (lookup φ i).isSome then 1 else 0) = (occurrences φ).length := by
  have h := FormulaBlockingCardinality.total_blocked φ
  simp_rw [FormulaBlockingCardinality.pairs_card_lookup] at h
  exact h

theorem switch_total (φ : CNF) :
    (∑ i : Fin (levels φ), ∑ a : V, degree φ (sw i a)) =
      30 * levels φ + 3 * (occurrences φ).length := by
  simp_rw [switch_level_total,Finset.sum_add_distrib]
  rw [predecessor_total,← Finset.mul_sum,real_lookup_total]
  simp
  ring

/-- Exact entity header of the existing source; no change to entity ordering. -/
theorem table_entities (φ : CNF) :
    (FormulaPACEncoding.table φ).entities =
      31 * levels φ + 4 * varCount φ + 2 * varCount φ * levels φ +
      3 * (occurrences φ).length := by
  rw [FormulaClauseDegree.table_after_external,switch_total]
  unfold levels
  ring

/-- Positive arithmetic form for the live occurrence/variable registers. -/
theorem table_entities_from_counts (φ : CNF) :
    (FormulaPACEncoding.table φ).entities = 31 +
      34 * (occurrences φ).length + 6 * varCount φ +
      2 * (occurrences φ).length * varCount φ := by
  rw [table_entities]
  unfold levels
  ring

end UnconstrainedPACDetection.FormulaHeaderCount

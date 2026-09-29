module

public import proofs.UnconstrainedPACDetection.FormulaLogicalConstruction

@[expose] public section

namespace UnconstrainedPACDetection.FormulaForward
open Complexity.SAT FormulaWiring FormulaRegions FormulaLogicalConstruction SwitchStack

theorem true_occurrence (φ : CNF) (α : Assignment) (hs : φ.eval α = true)
    (c : Fin φ.length) : ∃ i : Fin (levels φ), ∃ l,
      lookup φ i = some (c.val,l) ∧ l.eval α = true := by
  have hc := List.all_eq_true.mp hs _ (List.getElem_mem c.isLt)
  obtain ⟨l,hl,ht⟩ := List.any_eq_true.mp hc
  have hm : (c.val,l) ∈ occurrences φ := by
    simp only [occurrences,List.mem_flatMap,List.mem_map]
    refine ⟨(φ[c.val],c.val),?_,l,hl,rfl⟩
    exact List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem c.isLt)
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
  have hin : i < levels φ := by dsimp [levels]; omega
  refine ⟨⟨i,hin⟩,l,?_,ht⟩
  simpa only [lookup,List.getElem?_eq_getElem hi] using congrArg some he

theorem clause_step (φ : CNF) (α : Assignment) (hs : φ.eval α = true)
    (c : Fin φ.length) :
    Run φ α (.inr (.clause ⟨c.val,by omega⟩))
      (.inr (.clause ⟨c.val+1,by omega⟩)) := by
  obtain ⟨i,l,hl,ht⟩ := true_occurrence φ α hs c
  have hm : mode φ α i = true := by simp [mode,hl,ht]
  have hr : Run φ α (sw i 2) (sw i 6) := by
    simpa [hm] using data_reach φ (mode φ α) i
  have hi : RestrictedPaths.Edge (adjacency φ) (regionP φ (mode φ α))
      (.inr (.clause ⟨c.val,by omega⟩)) (sw i 2) := by
    refine ⟨?_,True.intro,?_⟩
    · exact ⟨Or.inl rfl,rfl,l,hl⟩
    · simp [regionP,sw,hm,data,ControlSwitch.leftData]
  have ho : RestrictedPaths.Edge (adjacency φ) (regionP φ (mode φ α))
      (sw i 6) (.inr (.clause ⟨c.val+1,by omega⟩)) := by
    refine ⟨?_,?_,True.intro⟩
    · exact ⟨Or.inr (Or.inl rfl),rfl,c.val,l,hl,rfl⟩
    · simp [regionP,sw,hm,data,ControlSwitch.leftData]
  exact (hr.head hi).tail ho

theorem clause_prefix (φ : CNF) (α : Assignment) (hs : φ.eval α = true) :
    ∀ c (hc : c ≤ φ.length), Run φ α (.inr (.clause ⟨0,by omega⟩))
      (.inr (.clause ⟨c,by omega⟩)) := by
  intro c
  induction c with
  | zero => intro hc; exact .refl
  | succ c ih =>
    intro hc
    exact (ih (by omega)).trans (clause_step φ α hs ⟨c,by omega⟩)

theorem logical_reach (φ : CNF) (α : Assignment) (hs : φ.eval α = true) :
    Run φ α (.inr (.var ⟨0,by omega⟩)) (sinkP φ) := by
  have hv := variable_prefix φ α (varCount φ) (by omega)
  have hj : RestrictedPaths.Edge (adjacency φ) (regionP φ (mode φ α))
      (.inr (.var ⟨varCount φ,by omega⟩)) (.inr (.clause ⟨0,by omega⟩)) :=
    ⟨⟨rfl,rfl⟩,True.intro,True.intro⟩
  exact (hv.tail hj).trans (clause_prefix φ α hs φ.length (by omega))

/-- Independent positive construction for every satisfying pinned assignment. -/
theorem sat_implies_accepted (φ : CNF) (hs : φ.Satisfiable) :
    ∃ p q, Accepted φ p q := by
  obtain ⟨α,hs⟩ := hs
  exact FormulaControlConstruction.accepted_of_logical_reach φ (mode φ α)
    (logical_reach φ α hs)

end UnconstrainedPACDetection.FormulaForward

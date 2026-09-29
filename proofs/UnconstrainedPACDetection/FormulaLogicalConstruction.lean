module

public import proofs.UnconstrainedPACDetection.FormulaControlConstruction

@[expose] public section

namespace UnconstrainedPACDetection.FormulaLogicalConstruction
open Complexity.SAT FormulaWiring FormulaRegions SwitchStack

def mode (φ : CNF) (α : Assignment) (i : Fin (levels φ)) : Bool :=
  match lookup φ i with
  | none => true
  | some (_,l) => l.eval α

abbrev Run (φ : CNF) (α : Assignment) :=
  RestrictedPaths.Reach (adjacency φ) (regionP φ (mode φ α))

theorem mode_false (φ : CNF) (α : Assignment) (i : Fin (levels φ))
    (v : Fin (varCount φ)) (h : blocked φ i v (α.get v.val) = true) :
    mode φ α i = false := by
  cases hl : lookup φ i with
  | none => simp [blocked,hl] at h
  | some z =>
    obtain ⟨c,l⟩ := z
    simp [blocked,hl] at h
    simp [mode,hl,Lit.eval,h.1,Ne.symm h.2]

theorem rail_step (φ : CNF) (α : Assignment) (v : Fin (varCount φ))
    (i : Fin (levels φ)) :
    Run φ α (.inr (.rail v (α.get v.val) ⟨i.val,by omega⟩))
      (.inr (.rail v (α.get v.val) ⟨i.val+1,by omega⟩)) := by
  cases hb : blocked φ i v (α.get v.val) with
  | false =>
    apply Relation.ReflTransGen.single
    refine ⟨?_,True.intro,True.intro⟩
    exact ⟨rfl,rfl,i.isLt,rfl,hb⟩
  | true =>
    have hm := mode_false φ α i v hb
    have hr : Run φ α (sw i 3) (sw i 7) := by
      simpa [hm] using data_reach φ (mode φ α) i
    have hi : RestrictedPaths.Edge (adjacency φ) (regionP φ (mode φ α))
        (.inr (.rail v (α.get v.val) ⟨i.val,by omega⟩)) (sw i 3) := by
      refine ⟨?_,True.intro,?_⟩
      · exact ⟨Or.inr rfl,rfl,rfl,hb⟩
      · simp [regionP,sw,hm,data,ControlSwitch.rightData]
    have ho : RestrictedPaths.Edge (adjacency φ) (regionP φ (mode φ α))
        (sw i 7) (.inr (.rail v (α.get v.val) ⟨i.val+1,by omega⟩)) := by
      refine ⟨?_,?_,True.intro⟩
      · exact ⟨Or.inr (Or.inr rfl),rfl,rfl,hb⟩
      · simp [regionP,sw,hm,data,ControlSwitch.rightData]
    exact (hr.head hi).tail ho

theorem rail_prefix (φ : CNF) (α : Assignment) (v : Fin (varCount φ)) :
    ∀ j (hj : j ≤ levels φ),
      Run φ α (.inr (.rail v (α.get v.val) ⟨0,by omega⟩))
        (.inr (.rail v (α.get v.val) ⟨j,by omega⟩)) := by
  intro j
  induction j with
  | zero => intro hj; exact .refl
  | succ j ih =>
    intro hj
    exact (ih (by omega)).trans (rail_step φ α v ⟨j,by omega⟩)

theorem variable_step (φ : CNF) (α : Assignment) (v : Fin (varCount φ)) :
    Run φ α (.inr (.var ⟨v.val,by omega⟩)) (.inr (.var ⟨v.val+1,by omega⟩)) := by
  have hr := rail_prefix φ α v (levels φ) (by omega)
  have hi : RestrictedPaths.Edge (adjacency φ) (regionP φ (mode φ α))
      (.inr (.var ⟨v.val,by omega⟩))
      (.inr (.rail v (α.get v.val) ⟨0,by omega⟩)) :=
    ⟨⟨rfl,rfl⟩,True.intro,True.intro⟩
  have ho : RestrictedPaths.Edge (adjacency φ) (regionP φ (mode φ α))
      (.inr (.rail v (α.get v.val) ⟨levels φ,by omega⟩))
      (.inr (.var ⟨v.val+1,by omega⟩)) :=
    ⟨⟨rfl,rfl⟩,True.intro,True.intro⟩
  exact (hr.head hi).tail ho

theorem variable_prefix (φ : CNF) (α : Assignment) :
    ∀ v (hv : v ≤ varCount φ), Run φ α (.inr (.var ⟨0,by omega⟩))
      (.inr (.var ⟨v,by omega⟩)) := by
  intro v
  induction v with
  | zero => intro hv; exact .refl
  | succ v ih =>
    intro hv
    exact (ih (by omega)).trans (variable_step φ α ⟨v,by omega⟩)

end UnconstrainedPACDetection.FormulaLogicalConstruction

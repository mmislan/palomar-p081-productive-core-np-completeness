module

public import proofs.UnconstrainedPACDetection.FormulaRegions

@[expose] public section

namespace UnconstrainedPACDetection.FormulaControlConstruction
open Complexity.SAT FormulaWiring FormulaRegions ControlSwitch SwitchStack

theorem control_members (φ : CNF) (mode : Fin (levels φ) → Bool) (i : Fin (levels φ)) :
    regionP φ mode (sw i 1) ∧ regionP φ mode (sw i 5) ∧
    regionQ φ mode (sw i 0) ∧ regionQ φ mode (sw i 4) := by
  cases h : mode i <;>
    simp [regionP,regionQ,sw,h,down,up,data,leftDown,rightDown,leftUp,rightUp]

theorem ascending (φ : CNF) (mode : Fin (levels φ) → Bool) :
    ∀ k (hk : k < levels φ), RestrictedPaths.Reach (adjacency φ) (regionP φ mode)
      (sourceP φ) (sw ⟨k,hk⟩ 5) := by
  intro k
  induction k with
  | zero => intro hk; exact down_reach φ mode ⟨0,hk⟩
  | succ k ih =>
    intro hk
    have hk' : k < levels φ := by omega
    have hj : RestrictedPaths.Edge (adjacency φ) (regionP φ mode)
        (sw ⟨k,hk'⟩ 5) (sw ⟨k+1,hk⟩ 1) :=
      ⟨Or.inr (Or.inl ⟨rfl,rfl,rfl⟩), (control_members φ mode _).2.1,
        (control_members φ mode _).1⟩
    exact ((ih hk').tail hj).trans (down_reach φ mode ⟨k+1,hk⟩)

theorem descending (φ : CNF) (mode : Fin (levels φ) → Bool) :
    ∀ k (hk : k < levels φ), RestrictedPaths.Reach (adjacency φ) (regionQ φ mode)
      (sw ⟨k,hk⟩ 0) (sinkQ φ) := by
  intro k
  induction k with
  | zero => intro hk; exact up_reach φ mode ⟨0,hk⟩
  | succ k ih =>
    intro hk
    have hk' : k < levels φ := by omega
    have hj : RestrictedPaths.Edge (adjacency φ) (regionQ φ mode)
        (sw ⟨k+1,hk⟩ 4) (sw ⟨k,hk'⟩ 0) :=
      ⟨Or.inr (Or.inr (Or.inl ⟨rfl,rfl,rfl⟩)), (control_members φ mode _).2.2.2,
        (control_members φ mode _).2.2.1⟩
    exact ((up_reach φ mode ⟨k+1,hk⟩).tail hj).trans (ih hk')

theorem controls_reach (φ : CNF) (mode : Fin (levels φ) → Bool) :
    RestrictedPaths.Reach (adjacency φ) (regionP φ mode) (sourceP φ)
      (.inr (.var ⟨0,by have := Nat.zero_lt_succ (varCount φ); omega⟩)) ∧
    RestrictedPaths.Reach (adjacency φ) (regionQ φ mode) (sourceQ φ) (sinkQ φ) := by
  have hn := levels_pos φ
  let top : Fin (levels φ) := ⟨levels φ-1,by omega⟩
  constructor
  · apply (ascending φ mode top.val top.isLt).tail
    refine ⟨?_,(control_members φ mode top).2.1,True.intro⟩
    simp [adjacency,Edge,DataWire,sw,top]
    omega
  · exact descending φ mode top.val top.isLt

/-- The remaining formula forward implication needs only the logical region walk. -/
theorem accepted_of_logical_reach (φ : CNF) (mode : Fin (levels φ) → Bool)
    (hlogic : RestrictedPaths.Reach (adjacency φ) (regionP φ mode)
      (.inr (.var ⟨0,by omega⟩)) (sinkP φ)) :
    ∃ p q, Accepted φ p q := by
  obtain ⟨hp,hq⟩ := controls_reach φ mode
  obtain ⟨p,q,ps,pt,qs,qt,pc,qc,pn,qn,hd⟩ :=
    RestrictedPaths.disjoint_pair (control_members φ mode ⟨0,levels_pos φ⟩).1
      (control_members φ mode ⟨levels φ-1,by have := levels_pos φ; omega⟩).2.2.1
      (regions_disjoint φ mode) (hp.trans hlogic) hq
  exact ⟨p,q,⟨pc,qc,pn,qn,hd,ps,pt,qs,qt⟩⟩

end UnconstrainedPACDetection.FormulaControlConstruction

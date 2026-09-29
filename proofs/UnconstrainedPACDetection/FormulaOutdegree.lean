module

public import proofs.UnconstrainedPACDetection.FormulaNormalization
public import proofs.UnconstrainedPACDetection.PACFormulaReduction

@[expose] public section

namespace UnconstrainedPACDetection.FormulaOutdegree
open Complexity.SAT FormulaWiring SwitchStack ControlSwitch

def degree (φ : CNF) (x : Vertex φ) : Nat :=
  Fintype.card {y : Vertex φ // adjacency φ x y}

def railNext (φ : CNF) (v : Fin (varCount φ)) (b : Bool) (j : Fin (levels φ+1)) :
    Vertex φ :=
  if hj : j.val < levels φ then
    if blocked φ ⟨j.val,hj⟩ v b then sw ⟨j.val,hj⟩ 3
    else .inr (.rail v b ⟨j.val+1,by omega⟩)
  else .inr (.var ⟨v.val+1,by have := v.isLt; omega⟩)

theorem rail_iff (φ : CNF) (v : Fin (varCount φ)) (b : Bool)
    (j : Fin (levels φ+1)) (y : Vertex φ) :
    adjacency φ (.inr (.rail v b j)) y ↔ y = railNext φ v b j := by
  by_cases hj : j.val < levels φ
  · by_cases hb : blocked φ ⟨j.val,hj⟩ v b = true
    · cases y with
      | inl y =>
        obtain ⟨i,a⟩ := y
        simp [sw,adjacency,Edge,DataWire,railNext,hj,hb,Fin.ext_iff]
        constructor
        · rintro ⟨_,ha,hji,_⟩; exact ⟨hji.symm,ha⟩
        · rintro ⟨hij,ha⟩
          have hi : i = ⟨j.val,hj⟩ := Fin.ext hij
          subst i
          exact ⟨Or.inr ha,ha,rfl,hb⟩
      | inr y =>
        cases y with
        | var w => simp [sw,adjacency,Edge,DataWire,railNext,hj,hb]; omega
        | clause c => simp [sw,adjacency,Edge,DataWire,railNext,hj,hb]
        | rail w c k => simp [sw,adjacency,Edge,DataWire,railNext,hj,hb]
    · have hb' : blocked φ ⟨j.val,hj⟩ v b = false := Bool.eq_false_iff.mpr hb
      cases y with
      | inl y =>
        obtain ⟨i,a⟩ := y
        simp [sw,adjacency,Edge,DataWire,railNext,hj,hb']
        intro _ _ hji
        have he : i = ⟨j.val,hj⟩ := Fin.ext hji.symm
        subst i
        exact hb'
      | inr y =>
        cases y with
        | var w => simp [adjacency,Edge,DataWire,railNext,hj,hb']; omega
        | clause c => simp [adjacency,Edge,DataWire,railNext,hj,hb']
        | rail w c k =>
          simp [adjacency,Edge,DataWire,railNext,hj,hb',Fin.ext_iff]
          tauto
  · have he : j.val = levels φ := by have := j.isLt; omega
    cases y with
    | inl y =>
      obtain ⟨i,a⟩ := y
      have hi := i.isLt
      simp [sw,adjacency,Edge,DataWire,railNext,hj]
      intro _ _ hji
      omega
    | inr y =>
      cases y with
      | var w => simp [adjacency,Edge,DataWire,railNext,he,Fin.ext_iff]
      | clause c => simp [adjacency,Edge,DataWire,railNext,hj]
      | rail w c k => simp [adjacency,Edge,DataWire,railNext,hj]

theorem rail_degree (φ : CNF) (v : Fin (varCount φ)) (b : Bool)
    (j : Fin (levels φ+1)) : degree φ (.inr (.rail v b j)) = 1 := by
  unfold degree
  have he := Fintype.card_congr (Equiv.subtypeEquivRight (rail_iff φ v b j))
  simpa using he

theorem rail_total (φ : CNF) :
    (∑ v : Fin (varCount φ), ∑ b : Bool, ∑ j : Fin (levels φ+1),
      degree φ (.inr (.rail v b j))) = 2 * varCount φ * (levels φ+1) := by
  simp only [rail_degree,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    Fintype.card_bool,smul_eq_mul]
  ring

end UnconstrainedPACDetection.FormulaOutdegree

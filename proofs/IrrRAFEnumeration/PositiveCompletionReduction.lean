module

public import proofs.IrrRAFEnumeration.PositiveCompletionAssignment

@[expose] public section

namespace IrrRAFEnumeration.PositiveCompletionCNF
open RAF Complexity.SAT PositiveRAFTrace

def certificateValue {d r : Nat} (Q : CRS (Fin d) (Fin r)) (S : Finset (Fin r)) :
    Atom d r → Bool
  | .inl j => decide (j ∈ S)
  | .inr (.inl (i,x)) => decide (x ∈ closureAt Q S i.val)
  | .inr (.inr (i,j)) => decide (j ∈ S ∧ Enabled Q (closureAt Q S i.val) j)

theorem formula_complete {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (h : PositiveCompletion.Available (IsRAF Q C) G.toFinset U) :
    (formula Q C G U).Satisfiable := by
  obtain ⟨S,hSU,hR,hG⟩ := h
  refine ⟨assignment (certificateValue Q S), (formula_eval_iff Q C G U _).mpr ?_⟩
  simp only [BitsCheck,assignment_select,assignment_row,assignment_fire,
    certificateValue,decide_eq_true_eq,decide_eq_false_iff_not]
  refine ⟨hR.1,?_,?_,?_,?_,?_,?_⟩
  · intro j hj hjs
    exact hj (hSU hjs)
  · intro x hx hxf
    exact hx hxf
  · intro i j
    exact ⟨And.left,fun x hx h => h.2 hx⟩
  · intro i x hx
    simp only [closureAt,closureStep,Finset.mem_union,Finset.mem_biUnion] at hx
    rcases hx with hx | ⟨j,hj,hout⟩
    · exact Or.inl hx
    · by_cases he : Enabled Q (closureAt Q S i.val) j
      · exact Or.inr ⟨j,by simpa only [ite_eq_left he] using hout,hj,he⟩
      · simp only [ite_eq_right he,Finset.notMem_empty] at hout
  · have hb := (isRAF_iff_bounded Q C S).mp hR
    simp only [Fintype.card_fin] at hb
    intro j
    refine ⟨?_,?_⟩
    · intro x hx hj
      exact (hb.2 j hj).1 hx
    · intro hj
      obtain ⟨x,hx,hc⟩ := (hb.2 j hj).2
      exact ⟨x,hc,hx⟩
  · intro I hI
    have hn := hG I (List.mem_toFinset.mpr hI)
    rw [Finset.subset_iff] at hn
    push Not at hn
    exact hn

/-- Exact semantic reduction to the actual SAT formula representation.
The separate encoded-input compiler and its TM runtime remain to be proved. -/
theorem formula_satisfiable_iff {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) :
    (formula Q C G U).Satisfiable ↔
      PositiveCompletion.Available (IsRAF Q C) G.toFinset U :=
  ⟨formula_sound Q C G U,formula_complete Q C G U⟩

end IrrRAFEnumeration.PositiveCompletionCNF

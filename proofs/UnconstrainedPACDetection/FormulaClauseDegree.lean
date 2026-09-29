module

public import proofs.UnconstrainedPACDetection.FormulaVariableDegree

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseDegree
open Complexity.SAT FormulaWiring SwitchStack FormulaOutdegree

private theorem clause_bound (φ : CNF) (i : Fin (levels φ)) {c : Nat} {l : Lit}
    (h : lookup φ i = some (c,l)) : c < φ.length := by
  obtain ⟨cl,hcl,_⟩ := ClauseSatisfaction.lookup_clause φ i h
  exact (List.getElem?_eq_some_iff.mp hcl).1

private def clauseEdge (φ : CNF) (i : Fin (occurrences φ).length) :
    {p : Fin (φ.length+1) × Vertex φ // adjacency φ (.inr (.clause p.1)) p.2} := by
  let o := (occurrences φ)[i.val]
  have hl : lookup φ i.castSucc = some o := by simp [lookup,o]
  let c : Fin (φ.length+1) := ⟨o.1,
    Nat.lt_succ_of_lt (clause_bound φ i.castSucc (c := o.1) (l := o.2) hl)⟩
  refine ⟨(c,sw i.castSucc 2),?_⟩
  simp [adjacency,Edge,DataWire,sw,c,hl]
  exact ⟨o.2,rfl⟩

private theorem clauseEdge_bijective (φ : CNF) : Function.Bijective (clauseEdge φ) := by
  constructor
  · intro i j h
    have he := congrArg (fun p => p.val.2) h
    change sw i.castSucc 2 = sw j.castSucc 2 at he
    simp only [sw,Sum.inl.injEq,Prod.mk.injEq,and_true] at he
    exact Fin.ext (congrArg (fun x : Fin (levels φ) => x.val) he)
  · rintro ⟨⟨c,y⟩,hy⟩
    cases y with
    | inr y => cases y <;> simp [adjacency,Edge,DataWire] at hy
    | inl y =>
      obtain ⟨j,a⟩ := y
      simp only [adjacency,Edge,DataWire,sw] at hy
      obtain ⟨_,rfl,l,hl⟩ := hy
      have hh := List.getElem?_eq_some_iff.mp hl
      let i : Fin (occurrences φ).length := ⟨j.val,hh.1⟩
      have hj : i.castSucc = j := Fin.ext rfl
      have ho : (occurrences φ)[i.val] = (c.val,l) := hh.2
      refine ⟨i,Subtype.ext ?_⟩
      apply Prod.ext
      · apply Fin.ext
        change ((occurrences φ)[i.val]).1 = c.val
        rw [ho]
      · change sw i.castSucc 2 = sw j 2
        exact congrArg (fun k => sw k 2) hj

theorem clause_total (φ : CNF) :
    (∑ c : Fin (φ.length+1), degree φ (.inr (.clause c))) = (occurrences φ).length := by
  let e : {p : Fin (φ.length+1) × Vertex φ // adjacency φ (.inr (.clause p.1)) p.2} ≃
      (Σ c : Fin (φ.length+1), {y : Vertex φ // adjacency φ (.inr (.clause c)) y}) :=
    { toFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
      invFun := fun p => ⟨(p.1,p.2.val),p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Fintype.card_congr ((Equiv.ofBijective (clauseEdge φ)
    (clauseEdge_bijective φ)).trans e)
  simpa [Fintype.card_sigma,degree] using h.symm

theorem table_after_external (φ : CNF) :
    (FormulaPACEncoding.table φ).entities =
      (∑ i : Fin (levels φ), ∑ a : ControlSwitch.V, degree φ (sw i a)) +
      (2 * varCount φ + 1) + 2 * varCount φ * (levels φ+1) +
      (occurrences φ).length := by
  rw [FormulaVariableDegree.table_after_rails_variables,clause_total]

end UnconstrainedPACDetection.FormulaClauseDegree

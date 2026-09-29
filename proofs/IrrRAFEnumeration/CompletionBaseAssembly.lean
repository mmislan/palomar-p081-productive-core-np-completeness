module

public import proofs.IrrRAFEnumeration.CompletionSupportFamily
public import proofs.IrrRAFEnumeration.PositiveBaseQuery

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM PositiveCompletionCNF

def initialFoodClauses {d r : Nat} (Q : CRS (Fin d) (Fin r)) : SAT.CNF :=
  each d (fun x => if x ∈ Q.food then [] else
    [negative [rowVar r ⟨0,by omega⟩ x]])

/-- Clause order chosen by the actual family emitters. -/
def assembledBase {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] : SAT.CNF :=
  [positive ((List.finRange r).map selectVar)] ++ initialFoodClauses Q ++
  (List.finRange d).flatMap (firingLayerClauses Q) ++
  (List.finRange d).flatMap (supportLayerClauses Q) ++
  (List.finRange r).flatMap (reactantClauses Q) ++
  (List.finRange r).map (@catalystClause d r C decC)

theorem assembledBase_eval_iff {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (a : SAT.Assignment) :
    SAT.CNF.eval a (assembledBase Q C) = true ↔
      SAT.CNF.eval a (baseFormula Q C) = true := by
  let cat : Fin r → SAT.Clause := fun j =>
    implies (selectVar j) (members (fun x => C x j) (rowVar r ⟨d,by omega⟩))
  have hcat : (@catalystClause d r C decC) = cat := by
    funext j
    rfl
  have hflat {α : Type} (xs : List α) (f : α → SAT.CNF) :
      SAT.CNF.eval a (xs.flatMap f) = true ↔
        ∀ x ∈ xs, SAT.CNF.eval a (f x) = true := by
    simp [SAT.CNF.eval,List.all_eq_true]
  have hnil : SAT.CNF.eval a [] = true := rfl
  unfold assembledBase baseFormula formula
  rw [hcat]
  simp only [initialFoodClauses,
    firingLayerClauses,firingClauses,supportLayerClauses,supportClause,
    reactantClauses,eval_append,hflat,eval_map,eval_each,
    eval_singleton,List.mem_finRange,forall_const,Finset.mem_univ,ite_true,
    List.map_nil,hnil,and_true,forall_and,forall_true_iff,and_assoc]
  rfl


/-- The assembled byte order is suitable for every dynamic completion query. -/
theorem assembledQuery_satisfiable_iff {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) :
    (assembledBase Q C ++ outputBlockers G ++ containerExclusions U).Satisfiable ↔
      PositiveCompletion.Available (IsRAF Q C) G.toFinset U := by
  rw [← baseQuery_satisfiable_iff (decC := decC) Q C G U]
  apply exists_congr
  intro a
  unfold baseQuery
  repeat rw [eval_append]
  rw [assembledBase_eval_iff (decC := decC)]

theorem original_food_cell {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (x : Fin d) :
    (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))).cells
      (d+r+3+x.val) = Γ.ofBool (decide (x ∈ Q.food)) := by
  have h := original_incidence_cell Q C (.inl x)
  have ha : d+r+3+(slotCode d r (.inl x)).val = d+r+3+x.val := by
    simp [slotCode,finSumFinEquiv]
  have hi : incidence Q C (Equiv.refl _) (Equiv.refl _) (.inl x) =
      decide (x ∈ Q.food) := by rfl
  rw [ha,hi] at h
  exact h

theorem original_food_maskClauses {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] :
    maskClauses (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
      (d+r+3) r d = initialFoodClauses Q := by
  have h := maskClauses_eq_each
    (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
    (d+r+3) r d (fun x => decide (x ∈ Q.food))
    (original_food_cell (decC := decC) Q C)
  unfold initialFoodClauses negative rowVar
  rw [h]
  apply congrArg (each d)
  funext x
  by_cases hx : x ∈ Q.food <;> simp [hx]

end IrrRAFEnumeration.CompletionQuery

module

public import proofs.UnconstrainedPACDetection.FormulaOrderedEnumeration

@[expose] public section

namespace UnconstrainedPACDetection.FormulaOrderedTable
open DirectedLinkageSource FormulaOrderedEnumeration

theorem table_nested {m n : Nat} (f : Fin n → Fin m → Nat) :
    GraphSourceTable.table f = (List.ofFn fun r => List.ofFn (f r)).flatten := by
  unfold GraphSourceTable.table
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext r
  apply congrArg List.ofFn
  funext x
  have he (h : r.val*m+x.val < n*m) :
      (⟨r.val*m+x.val,h⟩ : Fin (n*m)) = finProdFinEquiv (r,x) := by
    apply Fin.ext
    simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
  rw [he,Equiv.symm_apply_apply]

theorem table_lists {X Y : Type*} (xs : List X) (ys : List Y) (f : X → Y → Nat) :
    GraphSourceTable.table (fun r x => f (xs.get r) (ys.get x)) =
      xs.flatMap (fun r => ys.map (f r)) := by
  rw [table_nested]
  simp only [List.ofFn_comp',List.ofFn_get]
  rw [List.ofFn_comp' xs.get (fun r => ys.map (f r)),List.ofFn_get]
  rfl

variable {n : Nat} (A : Fin n → Fin n → Prop) [DecidableRel A]
  (T : (Bool ⊕ Bool) ↪ Fin n)

def rows : List (Bool ⊕ MarkedGraph.Internal T) :=
  [Sum.inl false,Sum.inl true] ++ (FiniteMarkedSource.internals T).map Sum.inr

def pairs := ((rows T).product (rows T)).filter
  (fun e => decide (FiniteMarkedSource.arcPredicate A T e))

def coefficient (right : Bool) (r : Bool ⊕ MarkedGraph.Internal T)
    (e : (Bool ⊕ MarkedGraph.Internal T) × (Bool ⊕ MarkedGraph.Internal T)) : Nat :=
  let z : Int := if r = tailRow e.1 then tailSign e.1
    else if r = headRow e.2 then headSign e.2 * factor e.1 * factor e.2 else 0
  if right then z.toNat else (-z).toNat

def values (right : Bool) : List Nat :=
  (rows T).flatMap (fun r => (pairs A T).map (coefficient T right r))

omit [DecidableRel A] in
theorem coefficient_source (right : Bool) (r : Bool ⊕ MarkedGraph.Internal T)
    (e : FromAdjacency.Arcs (MarkedGraph.pulled A T)) :
    coefficient T right r e.val =
      if right then (MarkedGraph.graphSource A T).right r e
      else (MarkedGraph.graphSource A T).left r e := by
  cases right <;> rfl

theorem side_table (right : Bool) :
    GraphSourceTable.table (fun r x => if right then
      (FiniteMarkedSource.numericSource A T).right r x else
      (FiniteMarkedSource.numericSource A T).left r x) = values A T right := by
  have hc r e := coefficient_source A T right r e
  change GraphSourceTable.table (fun r x => if right then
    (MarkedGraph.graphSource A T).right ((FiniteMarkedSource.ports T).get r)
      ((FiniteMarkedSource.arcList A T).get x) else
    (MarkedGraph.graphSource A T).left ((FiniteMarkedSource.ports T).get r)
      ((FiniteMarkedSource.arcList A T).get x)) = _
  simp_rw [← hc]
  rw [table_lists (FiniteMarkedSource.ports T) (FiniteMarkedSource.arcList A T)
    (fun r e => coefficient T right r e.val)]
  have hp : (FiniteMarkedSource.arcList A T).map Subtype.val = pairs A T := by
    rw [arc_values,ports_eq]
    rfl
  unfold values
  have hr : FiniteMarkedSource.ports T = rows T := ports_eq T
  rw [hr]
  apply congrArg (fun f => (rows T).flatMap f)
  funext r
  calc
    (FiniteMarkedSource.arcList A T).map
        (fun e => coefficient T right r e.val) =
        ((FiniteMarkedSource.arcList A T).map Subtype.val).map
          (coefficient T right r) := by
      induction FiniteMarkedSource.arcList A T with
      | nil => rfl
      | cons e es ih =>
        have hval : List.map Subtype.val (e :: es) =
            e.val :: List.map Subtype.val es := rfl
        rw [hval,List.map_cons,ih,List.map_cons]
    _ = (pairs A T).map (coefficient T right r) :=
      congrArg (List.map (coefficient T right r)) hp

/-- Exact canonical coefficient list: all left rows, then all right rows. -/
theorem dense_values :
    (FiniteMarkedSource.dense A T).values = values A T false ++ values A T true := by
  change GraphSourceTable.table (fun r x => (FiniteMarkedSource.numericSource A T).left r x) ++
    GraphSourceTable.table (fun r x => (FiniteMarkedSource.numericSource A T).right r x) = _
  have hl := side_table A T false
  have hr := side_table A T true
  simp only [Bool.false_eq_true,ite_false] at hl
  simp only [ite_true] at hr
  change List.append
    (GraphSourceTable.table (fun r x => (FiniteMarkedSource.numericSource A T).left r x))
    (GraphSourceTable.table (fun r x => (FiniteMarkedSource.numericSource A T).right r x)) =
    List.append (values A T false) (values A T true)
  exact congrArg₂ List.append hl hr

end UnconstrainedPACDetection.FormulaOrderedTable

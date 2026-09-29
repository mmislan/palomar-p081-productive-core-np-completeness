module

public import proofs.UnconstrainedPACDetection.FormulaSwitchTailHeads

@[expose] public section

namespace UnconstrainedPACDetection.FormulaHeadFieldOrder
open Complexity.SAT DirectedLinkageSource
open FormulaPairExecution (tailMeaning headMeaning)

def field (φ : CNF) (right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : List Bool :=
  if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ) (a,b)
  then BinaryFields.encodeField (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits
  else []

theorem arc_meaning (φ : CNF) (a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ) (a,b) ↔
      FormulaWiring.adjacency φ (tailMeaning φ a) (headMeaning φ b) := by
  change FormulaWiring.adjacency φ (tailMeaning φ a) (headMeaning φ b) ∧ tailVertex a ≠ headVertex b ↔ _
  constructor
  · exact fun h => h.1
  intro hadj
  refine ⟨hadj,?_⟩
  intro he
  have hh := congrArg (fun x => FormulaIndexedGraph.vertexEquiv φ (MarkedGraph.decode (FormulaIndexedGraph.terminals φ) x)) he
  change tailMeaning φ a = headMeaning φ b at hh
  rw [← hh] at hadj
  exact FormulaNormalization.no_loop φ _ hadj

theorem range_fields {X : Type*} (n : Nat) (f : Fin n → List X) :
    (List.range n).flatMap (fun k => if h : k<n then f ⟨k,h⟩ else []) = (List.finRange n).flatMap f := by
  have hv : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem
    · simp
    · intro i hi hj; simp
  rw [← hv,List.flatMap_map]
  apply congrArg (fun g => (List.finRange n).flatMap g)
  funext k
  simp [k.isLt]

theorem selected_fields {X Y : Type*} [DecidableEq X] (xs : List X)
    (P : X → Prop) [DecidablePred P] (hn : xs.Nodup) (f : {x // P x} → List Y)
    (g : X → List Y) (hf : ∀ x : {x // P x}, f x = g x.val)
    (hzero : ∀ x, ¬P x → g x = []) :
    (FiniteSubtypeEnumeration.selected xs P).flatMap f = xs.flatMap g := by
  have hmap := FormulaOrderedEnumeration.selected_values xs P hn
  have he : (FiniteSubtypeEnumeration.selected xs P).flatMap f =
      ((FiniteSubtypeEnumeration.selected xs P).map Subtype.val).flatMap g := by
    rw [List.flatMap_map]
    apply congrArg (fun g => (FiniteSubtypeEnumeration.selected xs P).flatMap g)
    funext x
    exact hf x
  rw [he,hmap]
  clear he hmap hn
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : P x
    · simp [hx,ih]
    · simp [hx,hzero x hx,ih]

theorem indexed_vertices (φ : CNF) :
    (List.finRange (FormulaIndexedGraph.labels φ).length).map (FormulaIndexedGraph.vertexEquiv φ) =
      FormulaIndexedGraph.labels φ := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_finRange]
    rfl

end UnconstrainedPACDetection.FormulaHeadFieldOrder

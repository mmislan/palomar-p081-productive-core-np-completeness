module

public import proofs.UnconstrainedPACDetection.FormulaOrderedTable

@[expose] public section

namespace UnconstrainedPACDetection.FormulaOrderedSchedule
open DirectedLinkageSource FormulaOrderedTable Complexity.SAT

theorem map_filter_scan {X Y : Type*} (xs : List X) (p : X → Bool) (f : X → Y) :
    (xs.filter p).map f = xs.flatMap (fun x => if p x then [f x] else []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h,ih]

variable {n : Nat} (A : Fin n → Fin n → Prop) [DecidableRel A]
  (T : (Bool ⊕ Bool) ↪ Fin n)

/-- Three ordered loops; rejected pairs emit nothing and accepted pairs one value. -/
def scan (right : Bool) : List Nat :=
  (rows T).flatMap fun r => (rows T).flatMap fun a => (rows T).flatMap fun b =>
    if FiniteMarkedSource.arcPredicate A T (a,b) then [coefficient T right r (a,b)] else []

theorem scan_eq (right : Bool) : scan A T right = values A T right := by
  unfold scan values pairs
  apply congrArg (fun f => (rows T).flatMap f)
  funext r
  rw [map_filter_scan]
  simp only [List.product,List.flatMap_assoc,List.flatMap_map,decide_eq_true_eq]

/-- Exact coefficient suffix supplied by the fused loop, without storing an arc list. -/
theorem dense_scan : (FiniteMarkedSource.dense A T).values =
    scan A T false ++ scan A T true := by
  rw [scan_eq,scan_eq,dense_values]

def bits : List Bool :=
  (scan A T false ++ scan A T true).flatMap (fun z => BinaryFields.encodeField z.bits)

theorem dense_encode : (FiniteMarkedSource.dense A T).encode =
    BinaryFields.encodeField (FiniteMarkedSource.dense A T).entities.bits ++
    BinaryFields.encodeField (FiniteMarkedSource.dense A T).reactions.bits ++ bits A T := by
  unfold BinarySourceData.DenseSource.encode BinaryFields.encode
  rw [dense_scan]
  simp only [List.flatMap_cons,List.flatMap_map,List.append_assoc,bits]

/-- The exact existing formula encoding is headers followed by the fused schedule. -/
theorem formula_encode (φ : CNF) : FormulaPACEncoding.encode φ =
    BinaryFields.encodeField (FormulaPACEncoding.table φ).entities.bits ++
    BinaryFields.encodeField (FormulaPACEncoding.table φ).reactions.bits ++
    bits (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ) :=
  dense_encode _ _

end UnconstrainedPACDetection.FormulaOrderedSchedule

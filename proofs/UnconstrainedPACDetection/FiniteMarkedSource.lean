module

public import proofs.UnconstrainedPACDetection.FiniteSubtypeEnumeration
public import proofs.UnconstrainedPACDetection.MarkedGraphSource
public import proofs.UnconstrainedPACDetection.GraphSourceTable

@[expose] public section

namespace UnconstrainedPACDetection.FiniteMarkedSource
open DirectedLinkageSource FiniteSubtypeEnumeration

variable {n : Nat} (A : Fin n → Fin n → Prop) [DecidableRel A]
  (T : (Bool ⊕ Bool) ↪ Fin n)

instance internalPredicate : DecidablePred (fun x : Fin n => x ∉ Set.range T) :=
  fun x => inferInstanceAs (Decidable (¬∃ b : Bool ⊕ Bool, T b = x))

def internals : List (MarkedGraph.Internal T) :=
  selected (List.finRange n) (fun x => x ∉ Set.range T)

theorem mem_internals (x : MarkedGraph.Internal T) : x ∈ internals T := by
  exact (mem_selected _ _ x).mpr (List.mem_finRange x.val)

def ports : List (Bool ⊕ MarkedGraph.Internal T) :=
  ([Sum.inl false,Sum.inl true] ++ (internals T).map Sum.inr).dedup

theorem mem_ports (x : Bool ⊕ MarkedGraph.Internal T) : x ∈ ports T := by
  cases x with
  | inl b => cases b <;> simp [ports]
  | inr x => simp [ports,mem_internals]

def rowEquiv : Fin (ports T).length ≃ Bool ⊕ MarkedGraph.Internal T :=
  List.Nodup.getEquivOfForallMemList (ports T) (List.nodup_dedup _) (mem_ports T)

def arcPredicate (e : (Bool ⊕ MarkedGraph.Internal T) × (Bool ⊕ MarkedGraph.Internal T)) : Prop :=
  MarkedGraph.pulled A T (tailVertex e.1) (headVertex e.2) ∧
    tailVertex e.1 ≠ headVertex e.2

instance arcDecidable : DecidablePred (arcPredicate A T) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

def arcList : List (FromAdjacency.Arcs (MarkedGraph.pulled A T)) :=
  selected ((ports T).product (ports T)) (arcPredicate A T)

theorem mem_arcList (x : FromAdjacency.Arcs (MarkedGraph.pulled A T)) : x ∈ arcList A T := by
  apply (mem_selected _ _ x).mpr
  exact List.mem_product.mpr ⟨mem_ports T x.val.1,mem_ports T x.val.2⟩

def entityEquiv : Fin (arcList A T).length ≃ FromAdjacency.Arcs (MarkedGraph.pulled A T) :=
  List.Nodup.getEquivOfForallMemList (arcList A T) (nodup_selected _ _) (mem_arcList A T)

def numericSource : ReversibleSource (Fin (arcList A T).length) (Fin (ports T).length) :=
  (MarkedGraph.graphSource A T).reindex (entityEquiv A T) (rowEquiv T)

def dense : BinarySourceData.DenseSource := GraphSourceTable.dense (numericSource A T)

theorem decode_dense : BinarySourceData.decode (dense A T).encode = some (dense A T) :=
  GraphSourceTable.decode_encode _

theorem dense_pac_iff : (∃ c, (dense A T).toSource.PAC c) ↔
    DirectedPathNormalization.Linkage A (T (.inl false)) (T (.inl true))
      (T (.inr false)) (T (.inr true)) := by
  classical
  rw [dense,GraphSourceTable.toSource_dense]
  have back : (numericSource A T).reindex (entityEquiv A T).symm (rowEquiv T).symm =
      MarkedGraph.graphSource A T := by
    simp only [numericSource,ReversibleSource.reindex,Equiv.apply_symm_apply]
  have he : (∃ c, (numericSource A T).PAC c) ↔ ∃ c, (MarkedGraph.graphSource A T).PAC c := by
    constructor
    · exact exists_pac_of_reindex _ _ _
    · intro h
      apply exists_pac_of_reindex _ (entityEquiv A T).symm (rowEquiv T).symm
      rw [back]
      exact h
  exact he.trans (MarkedGraph.pac_iff_marked_linkage A T)

end UnconstrainedPACDetection.FiniteMarkedSource

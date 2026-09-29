module

public import proofs.UnconstrainedPACDetection.FormulaVariableTailHeads

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVariableTailCanonical
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaPairExecution (tailMeaning)
open FormulaVertexHeadFields (vertex)
open FormulaHeadFieldOrder (field)

theorem isolated {X Y : Type} [DecidableEq X] (xs : List X) (hn : xs.Nodup)
    (x : X) (hx : x ∈ xs) (f : X → List Y) :
    xs.flatMap (fun y => if y=x then f y else []) = f x := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rw [List.nodup_cons] at hn
    by_cases h : a=x
    · subst a
      have hz : xs.flatMap (fun y => if y=x then f y else []) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro y hy
        exact ite_eq_right (by intro he; subst y; exact hn.1 hy)
      simp only [List.flatMap_cons,ite_true,hz,List.append_nil]
    · have hm : x ∈ xs := (List.mem_cons.mp hx).resolve_left (Ne.symm h)
      simpa only [List.flatMap_cons,ite_eq_right h,List.nil_append] using ih hn.2 hm

theorem variable_vertex (φ : SAT.CNF) (v : Fin (varCount φ)) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var v.castSucc)) (x : FormulaWiring.Vertex φ) :
    vertex φ right r a x =
      match x with
      | .inr (.rail w s j) => if w=v ∧ j=0 then field φ right r a (FormulaRailCursor.port φ w s j) else []
      | _ => [] := by
  cases x with
  | inl x =>
    apply FormulaClauseTailCanonical.vertex_zero
    rw [ha]
    simp [FormulaWiring.adjacency,SwitchStack.Edge,SwitchStack.sw,FormulaWiring.DataWire]
  | inr x =>
    cases x with
    | var w =>
      apply FormulaClauseTailCanonical.vertex_zero
      rw [ha]
      simp [FormulaWiring.adjacency,SwitchStack.Edge,FormulaWiring.DataWire]
    | clause c =>
      apply FormulaClauseTailCanonical.vertex_zero
      rw [ha]
      have hv := v.isLt
      simp [FormulaWiring.adjacency,SwitchStack.Edge,FormulaWiring.DataWire]
      omega
    | rail w s j =>
      change vertex φ right r a (.inr (.rail w s j)) =
        if w=v ∧ j=0 then field φ right r a (FormulaRailCursor.port φ w s j) else []
      have he := FormulaVertexHeadFields.of_internal φ right r a (FormulaRailCursor.port φ w s j) rfl
      rw [FormulaRailCursor.port_meaning] at he
      by_cases h : w=v ∧ j=0
      · simpa only [ite_eq_left h] using he
      · rw [ite_eq_right h]
        apply FormulaClauseTailCanonical.vertex_zero
        rw [ha]
        simp only [FormulaWiring.adjacency,SwitchStack.Edge,FormulaWiring.DataWire]
        intro hh
        apply h
        exact ⟨Fin.ext hh.1.symm,Fin.ext hh.2⟩

theorem bits_eq (φ : SAT.CNF) (v : Fin (varCount φ)) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var v.castSucc)) :
    field φ right r a (FormulaRailCursor.port φ v false 0) ++
      field φ right r a (FormulaRailCursor.port φ v true 0) =
      (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (field φ right r a) := by
  have hn {X : Type} (xs : List X) : xs.flatMap (fun _ => ([] : List Bool)) = [] :=
    List.flatMap_eq_nil_iff.mpr (by intro x hx; rfl)
  have hj (w : Fin (varCount φ)) (s : Bool) :
      (List.finRange (levels φ+1)).flatMap (fun j =>
        if w=v ∧ j=0 then field φ right r a (FormulaRailCursor.port φ w s j) else []) =
        if w=v then field φ right r a (FormulaRailCursor.port φ w s 0) else [] := by
    by_cases hw : w=v
    · simp only [hw,true_and,ite_true]
      exact isolated _ (List.nodup_finRange _) 0 (List.mem_finRange 0) _
    · simp only [hw,false_and,ite_false,hn]
  have hv := congrArg (fun xs => xs.flatMap (vertex φ right r a))
    (FormulaOrderedEnumeration.labels_eq_vertices φ)
  simp only [FormulaEnumeration.vertices,List.flatMap_append,List.flatMap_assoc,List.flatMap_map,
    variable_vertex φ v right r a ha,SwitchStack.sw,hn,hj,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.nil_append] at hv
  have hw : (List.finRange (varCount φ)).flatMap (fun w =>
      (if w=v then field φ right r a (FormulaRailCursor.port φ w false 0) else []) ++
      (if w=v then field φ right r a (FormulaRailCursor.port φ w true 0) else [])) =
      field φ right r a (FormulaRailCursor.port φ v false 0) ++
      field φ right r a (FormulaRailCursor.port φ v true 0) := by
    have he (w : Fin (varCount φ)) (A B : List Bool) :
        (if w=v then A else []) ++ (if w=v then B else []) = if w=v then A++B else [] := by
      split <;> simp_all
    simp only [he]
    exact isolated _ (List.nodup_finRange _) v (List.mem_finRange v) _
  rw [hw] at hv
  have hm (s : Bool) : FormulaMergedHeads.field φ right r a s = [] := by
    change field φ right r a (.inl s) = []
    unfold field
    apply ite_eq_right
    rw [FormulaHeadFieldOrder.arc_meaning,ha,FormulaMergedHeads.merged_meaning]
    have hv := v.isLt
    cases s <;> simp [FormulaWiring.sinkP,FormulaWiring.sinkQ,FormulaWiring.adjacency,
      SwitchStack.Edge,SwitchStack.sw,FormulaWiring.DataWire]
    omega
  have hh := FormulaVertexHeadFields.head_scan φ right r a
  rw [hv] at hh
  simpa only [hm,List.nil_append] using hh.symm

theorem canonical_hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var v.castSucc)) (i j b f M : Nat) (ys : List Bool)
    (hL : levels φ ≤ M) (hV : varCount φ ≤ M) (hv : v.val ≤ M) (hb : b ≤ M)
    (hs : ∀ s, FormulaRailBase.value (levels φ) (varCount φ) v.val s ≤ M) :
    (FormulaVariableTailHeads.machine right
      (FormulaCoefficientPlan.choose right (FormulaCoefficientPlan.tag r) (FormulaCoefficientPlan.tag a) none)).HoareTime
      (EmitPred (VerifierPairRestore.word φ.encode)
        (FormulaRailHeadPrepare.bank i v.val j (FormulaCoefficientPlan.index r) (FormulaCoefficientPlan.index a)
          b f (levels φ) (varCount φ)) ys)
      (EmitPred (VerifierPairRestore.word φ.encode)
        (FormulaRailHeadPrepare.bank i v.val j (FormulaCoefficientPlan.index r) (FormulaCoefficientPlan.index a)
          (FormulaRailBase.value (levels φ) (varCount φ) v.val true) f (levels φ) (varCount φ))
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (field φ right r a)))
      (80*(opBudget M+1)+6*(FormulaIndexedGraph.labels φ).length+57) := by
  have h := FormulaVariableTailHeads.hoare φ v right r a ha i j b f M ys hL hV hv hb hs
  rw [List.append_assoc,bits_eq φ v right r a ha] at h
  exact h

end UnconstrainedPACDetection.FormulaVariableTailCanonical

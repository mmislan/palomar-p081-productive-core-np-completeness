module

public import proofs.UnconstrainedPACDetection.FormulaClauseTailPrepare

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseTailCanonical
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word)
open FormulaWiring (levels varCount)
open FormulaPairExecution (tailMeaning headMeaning)
open FormulaCoefficientPlan (choose tag index)
open FormulaVertexHeadFields (vertex)
open FormulaHeadFieldOrder (field)

theorem vertex_zero (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (y : FormulaWiring.Vertex φ)
    (hy : ¬FormulaWiring.adjacency φ (tailMeaning φ a) y) : vertex φ right r a y = [] := by
  by_cases ht : (FormulaIndexedGraph.vertexEquiv φ).symm y ∉ Set.range (FormulaIndexedGraph.terminals φ)
  · rw [FormulaVertexHeadFields.nonterminal φ right r a y ht]
    exact ite_eq_right hy
  · unfold vertex FormulaVertexHeadFields.indexed
    exact dite_eq_right ht

theorem external_zero (φ : SAT.CNF) (c : Fin φ.length) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.clause c.castSucc)) (x : FormulaWiring.External φ) :
    vertex φ right r a (.inr x) = [] := by
  apply vertex_zero
  rw [ha]
  cases x <;> simp [FormulaWiring.adjacency,SwitchStack.Edge,FormulaWiring.DataWire]

theorem switch_field (φ : SAT.CNF) (c : Fin φ.length) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.clause c.castSucc)) (i : Fin (levels φ)) (q : ControlSwitch.V) :
    vertex φ right r a (SwitchStack.sw i q) =
      if q=2 then field φ right r a (FormulaClauseSwitchCursor.port φ i) else [] := by
  by_cases hq : q=2
  · subst q
    have h := FormulaVertexHeadFields.of_internal φ right r a (FormulaClauseSwitchCursor.port φ i) rfl
    rw [FormulaClauseSwitchCursor.port_meaning] at h
    simpa only [ite_true] using h
  · rw [ite_eq_right hq]
    apply vertex_zero
    rw [ha]
    simp [FormulaWiring.adjacency,SwitchStack.Edge,SwitchStack.sw,FormulaWiring.DataWire,hq]

theorem single_port {X : Type*} (f : ControlSwitch.V → List X) :
    (List.finRange 20).flatMap (fun q => if q=2 then f q else []) = f 2 := by
  have h : List.finRange 20 = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := by decide
  rw [h]
  norm_num [Fin.ext_iff]

theorem merged_zero (φ : SAT.CNF) (c : Fin φ.length) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.clause c.castSucc)) (s : Bool) : field φ right r a (.inl s) = [] := by
  unfold field
  apply ite_eq_right
  rw [FormulaHeadFieldOrder.arc_meaning,ha,FormulaMergedHeads.merged_meaning]
  cases s with
  | false => simp [FormulaWiring.sinkP,FormulaWiring.adjacency,SwitchStack.Edge,FormulaWiring.DataWire]
  | true => simp [FormulaWiring.sinkQ,FormulaWiring.adjacency,SwitchStack.Edge,SwitchStack.sw,FormulaWiring.DataWire]

theorem bits_eq (φ : SAT.CNF) (c : Fin φ.length) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.clause c.castSucc)) :
    FormulaClauseTailHeads.bits φ right r a (levels φ) =
      (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (field φ right r a) := by
  have hv := congrArg (fun xs => xs.flatMap (vertex φ right r a)) (FormulaOrderedEnumeration.labels_eq_vertices φ)
  simp only [FormulaEnumeration.vertices,List.flatMap_append,List.flatMap_assoc,List.flatMap_map] at hv
  simp only [external_zero φ c right r a ha,switch_field φ c right r a ha,single_port] at hv
  have hr := FormulaHeadFieldOrder.range_fields (levels φ)
    (fun i => field φ right r a (FormulaClauseSwitchCursor.port φ i))
  change FormulaClauseTailHeads.bits φ right r a (levels φ) = _ at hr
  have hh := FormulaVertexHeadFields.head_scan φ right r a
  rw [hv,← hr] at hh
  have hz0 : FormulaMergedHeads.field φ right r a false = [] := merged_zero φ c right r a ha false
  have hz1 : FormulaMergedHeads.field φ right r a true = [] := merged_zero φ c right r a ha true
  have hn {X : Type} (xs : List X) : xs.flatMap (fun _ => ([] : List Bool)) = [] :=
    List.flatMap_eq_nil_iff.mpr (by intro x hx; rfl)
  simpa only [hz0,hz1,hn,List.nil_append,List.append_nil] using hh.symm

theorem canonical_hoare (φ : SAT.CNF) (c : Fin φ.length) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.clause c.castSucc)) (i b f : Nat) (ys : List Bool) :
    (FormulaClauseTailPrepare.machine right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (FormulaClauseTailHeads.frame i c.val (index r) (index a) b
        (levels φ) (varCount φ) φ.length (regTape f)) ys)
      (EmitPred (word φ.encode) (FormulaClauseTailHeads.frame (levels φ) c.val (index r) (index a) (20*levels φ+2)
        (levels φ) (varCount φ) φ.length (regTape (levels φ)))
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap (field φ right r a)))
      (2*i+2*b+2*f+2*(levels φ)^2+7*levels φ+38+FormulaClauseTailHeads.loopBudget φ) := by
  rw [← bits_eq φ c right r a ha]
  exact FormulaClauseTailPrepare.hoare φ c right r a ha i b f ys

end UnconstrainedPACDetection.FormulaClauseTailCanonical

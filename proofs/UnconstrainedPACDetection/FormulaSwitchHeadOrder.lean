module

public import proofs.UnconstrainedPACDetection.FormulaVertexHeadFields

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchHeadOrder
open Complexity.SAT DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaPairExecution (tailMeaning)
open FormulaCoefficientPlan (choose tag index)
open FormulaVertexHeadFields (vertex raw)

theorem source_zero (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (s : Bool) :
    raw φ right r a (PACFormulaReduction.terminals φ (.inl s)) = [] := by
  cases s with
  | false => simp [raw,PACFormulaReduction.terminals,PACFormulaReduction.terminal,FormulaNormalization.no_into_sourceP]
  | true => simp [raw,PACFormulaReduction.terminals,PACFormulaReduction.terminal,FormulaNormalization.no_into_sourceQ]

theorem vertex_switch (φ : CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (j : Fin (levels φ)) (q : ControlSwitch.V) :
    vertex φ right r a (SwitchStack.sw j q) =
      if j.val=0 ∧ q=4 then [] else raw φ right r a (SwitchStack.sw j q) := by
  by_cases ht : SwitchStack.sw j q ∈ Set.range (PACFormulaReduction.terminals φ)
  · obtain ⟨t,he⟩ := ht
    have hv := FormulaVertexHeadFields.terminal φ right r a t
    rw [he] at hv
    cases t with
    | inl s =>
      have hz := source_zero φ right r a s
      rw [he] at hz
      simp only [hv,hz,ite_self]
    | inr s =>
      cases s with
      | false => simp [PACFormulaReduction.terminals,PACFormulaReduction.terminal,FormulaWiring.sinkP,SwitchStack.sw] at he
      | true =>
        have hp : (⟨0,FormulaWiring.levels_pos φ⟩ : Fin (levels φ))=j ∧ (4 : ControlSwitch.V)=q := by
          simpa [PACFormulaReduction.terminals,PACFormulaReduction.terminal,FormulaWiring.sinkQ,SwitchStack.sw] using he
        have hs : j.val=0 ∧ q=4 := ⟨(congrArg Fin.val hp.1).symm,hp.2.symm⟩
        simp only [hv,ite_eq_left hs]
  · have hv := FormulaVertexHeadFields.nonterminal φ right r a (SwitchStack.sw j q)
      ((FormulaVertexHeadFields.internal_iff φ _).mpr ht)
    have hs : ¬(j.val=0 ∧ q=4) := by
      rintro ⟨hj,hq⟩
      apply ht
      refine ⟨.inr true,?_⟩
      have hj' : j=⟨0,FormulaWiring.levels_pos φ⟩ := Fin.ext hj
      subst j; subst q
      rfl
    simp only [hv,ite_eq_right hs]

theorem raw_switch (φ : CNF) (i j : Fin (levels φ)) (p q : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) :
    raw φ right r a (SwitchStack.sw j q) = FormulaSwitchHeadRound.field φ i j p q right
      (choose right (tag r) (tag a) none) (index r) (index a) (20*j.val+q.val) := by
  unfold raw FormulaSwitchHeadRound.field
  rw [ha,FormulaSwitchCursor.index]

theorem port_fields (φ : CNF) (i j : Fin (levels φ)) (p : ControlSwitch.V)
    (skipSink right : Bool) (plan : FormulaCoefficientPlan.Plan) (r a : Nat) :
    FormulaSwitchHeadPorts.fields φ i j p skipSink right plan r a (List.finRange 20) (20*j.val) =
      (List.finRange 20).flatMap (fun q => if skipSink && decide (q=4) then [] else
        FormulaSwitchHeadRound.field φ i j p q right plan r a (20*j.val+q.val)) := by
  rfl

theorem level_fields (φ : CNF) (i j : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) :
    FormulaSwitchHeadLevels.fields φ i j p (decide (j.val=0)) right
      (choose right (tag r) (tag a) none) (index r) (index a) =
      (List.finRange 20).flatMap (fun q => vertex φ right r a (SwitchStack.sw j q)) := by
  unfold FormulaSwitchHeadLevels.fields
  rw [port_fields]
  apply congrArg (fun f => (List.finRange 20).flatMap f)
  funext q
  rw [vertex_switch,raw_switch φ i j p q right r a ha]
  by_cases hj : j.val=0 <;> simp [hj]

theorem first_rest {X : Type*} (n : Nat) (hn : 0<n) (f : Fin n → List X) :
    (List.finRange n).flatMap f = f ⟨0,hn⟩ ++
      (List.range (n-1)).flatMap (fun k => if hk : k+1<n then f ⟨k+1,hk⟩ else []) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [List.finRange_succ,List.flatMap_cons,List.flatMap_map]
    congr 1
    rw [← FormulaHeadFieldOrder.range_fields n (fun v => f v.succ)]
    apply congrArg (fun g => (List.range n).flatMap g)
    funext k
    by_cases hk : k<n
    · simp only [hk,dite_true,Nat.add_lt_add_iff_right]
      apply congrArg f
      exact Fin.ext rfl
    · have hk' : ¬k+1<n+1 := by omega
      simp only [hk,hk',dite_false]

theorem all_levels (φ : CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) :
    FormulaAllSwitchHeads.bits φ i p right (choose right (tag r) (tag a) none) (index r) (index a) =
      (List.finRange (levels φ)).flatMap (fun j =>
        (List.finRange 20).flatMap (fun q => vertex φ right r a (SwitchStack.sw j q))) := by
  rw [first_rest _ (FormulaWiring.levels_pos φ)]
  unfold FormulaAllSwitchHeads.bits
  congr 1
  · exact level_fields φ i ⟨0,FormulaWiring.levels_pos φ⟩ p right r a ha
  · unfold FormulaSwitchHeadLevels.laterBits
    apply congrArg (fun f => (List.range (levels φ-1)).flatMap f)
    funext k
    unfold FormulaSwitchHeadLevels.laterField
    split
    next hk =>
      simpa only [show decide ((⟨k+1,hk⟩ : Fin (levels φ)).val=0) = false by simp] using
        level_fields φ i ⟨k+1,hk⟩ p right r a ha
    next => rfl

end UnconstrainedPACDetection.FormulaSwitchHeadOrder

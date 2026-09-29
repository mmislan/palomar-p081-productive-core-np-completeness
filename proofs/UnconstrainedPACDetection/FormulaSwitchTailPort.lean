module

public import proofs.UnconstrainedPACDetection.FormulaSwitchTailReentrant

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchTailPort
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaPairExecution (tailMeaning)
open FormulaCoefficientPlan (tag index)
open FormulaVertexTailFields (vertex)
open VerifierPairRestore (word)

def Admissible (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) : Prop :=
  (p=0 → i.val+1 ≠ levels φ) ∧ (p=1 → i.val ≠ 0) ∧ (p=4 → i.val ≠ 0)

theorem internal (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (h : Admissible φ i p) :
    (FormulaIndexedGraph.vertexEquiv φ).symm (SwitchStack.sw i p) ∉ Set.range (FormulaIndexedGraph.terminals φ) := by
  rintro ⟨t,ht⟩
  have he := congrArg (FormulaIndexedGraph.vertexEquiv φ) ht
  cases t with
  | inl t =>
    cases t with
    | false =>
      simp [FormulaIndexedGraph.terminals,PACFormulaReduction.terminals,PACFormulaReduction.terminal,
        FormulaWiring.sourceP,SwitchStack.sw] at he
      have hv := congrArg Fin.val he.1
      exact h.2.1 he.2.symm hv.symm
    | true =>
      simp [FormulaIndexedGraph.terminals,PACFormulaReduction.terminals,PACFormulaReduction.terminal,
        FormulaWiring.sourceQ,SwitchStack.sw] at he
      have hv := congrArg Fin.val he.1
      have hl := FormulaWiring.levels_pos φ
      change levels φ - 1 = i.val at hv
      exact h.1 he.2.symm (by omega)
  | inr t =>
    cases t with
    | false =>
      simp [FormulaIndexedGraph.terminals,PACFormulaReduction.terminals,PACFormulaReduction.terminal,
        FormulaWiring.sinkP,SwitchStack.sw] at he
    | true =>
      simp [FormulaIndexedGraph.terminals,PACFormulaReduction.terminals,PACFormulaReduction.terminal,
        FormulaWiring.sinkQ,SwitchStack.sw] at he
      have hv := congrArg Fin.val he.1
      exact h.2.2 he.2.symm hv.symm

def port (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (h : Admissible φ i p) :
    Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ) :=
  .inr ⟨(FormulaIndexedGraph.vertexEquiv φ).symm (SwitchStack.sw i p),internal φ i p h⟩

theorem port_meaning (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (h : Admissible φ i p) :
    tailMeaning φ (port φ i p h) = SwitchStack.sw i p := by
  simp [tailMeaning,port,tailVertex,MarkedGraph.decode]

theorem port_index (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (h : Admissible φ i p) :
    index (port φ i p h) = 20*i.val+p.val := FormulaSwitchCursor.index φ i p

theorem first_source (φ : SAT.CNF) (i : Fin (levels φ)) (hi : i.val=0) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : vertex φ right r (SwitchStack.sw i 1) = [] := by
  have he : i = ⟨0,FormulaWiring.levels_pos φ⟩ := Fin.ext hi
  subst i
  exact FormulaVertexTailFields.terminal φ right r (.inl false)

theorem first_sink (φ : SAT.CNF) (i : Fin (levels φ)) (hi : i.val=0) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : vertex φ right r (SwitchStack.sw i 4) = [] := by
  have he : i = ⟨0,FormulaWiring.levels_pos φ⟩ := Fin.ext hi
  subst i
  exact FormulaVertexTailFields.terminal φ right r (.inr true)

theorem last_source (φ : SAT.CNF) (i : Fin (levels φ)) (hi : i.val+1=levels φ) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : vertex φ right r (SwitchStack.sw i 0) = [] := by
  have hl := FormulaWiring.levels_pos φ
  have he : i = ⟨levels φ-1,by omega⟩ := Fin.ext (show i.val = levels φ-1 by omega)
  rw [he]
  exact FormulaVertexTailFields.terminal φ right r (.inl true)

theorem hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (hp : Admissible φ i p) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (FormulaSwitchTailReentrant.machine p right (tag r) none).HoareTime
      (EmitPred (word φ.encode) (FormulaSwitchTailReentrant.frame i.val (index r) (20*i.val+p.val)
        (levels φ) (varCount φ) φ.length) ys)
      (EmitPred (word φ.encode) (FormulaSwitchTailReentrant.frame i.val (index r) (20*i.val+p.val)
        (levels φ) (varCount φ) φ.length) (ys ++ vertex φ right r (SwitchStack.sw i p)))
      (FormulaSwitchTailReentrant.budget φ) := by
  let a := port φ i p hp
  have ht : tag a = none := rfl
  have h := FormulaSwitchTailReentrant.hoare φ i p right r a (port_meaning φ i p hp) ys
  have hv := FormulaVertexTailFields.of_internal φ right r a ht
  rw [port_meaning] at hv
  rw [ht,port_index,← hv] at h
  exact h

end UnconstrainedPACDetection.FormulaSwitchTailPort

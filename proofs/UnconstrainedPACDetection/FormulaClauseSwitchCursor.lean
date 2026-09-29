module

public import proofs.UnconstrainedPACDetection.FormulaSwitchTailCanonical

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseSwitchCursor
open Complexity.SAT FormulaWiring DirectedLinkageSource
open FormulaPairExecution (headMeaning)

def port (φ : CNF) (i : Fin (levels φ)) : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ) :=
  .inr ⟨(FormulaIndexedGraph.vertexEquiv φ).symm (SwitchStack.sw i 2),by
    rintro ⟨t,ht⟩
    have h := congrArg (FormulaIndexedGraph.vertexEquiv φ) ht
    cases t with
    | inl t => cases t <;> simp [FormulaIndexedGraph.terminals,PACFormulaReduction.terminals,
        PACFormulaReduction.terminal,sourceP,sourceQ,SwitchStack.sw] at h
    | inr t => cases t <;> simp [FormulaIndexedGraph.terminals,PACFormulaReduction.terminals,
        PACFormulaReduction.terminal,sinkP,sinkQ,SwitchStack.sw] at h⟩

theorem port_meaning (φ : CNF) (i : Fin (levels φ)) : headMeaning φ (port φ i) = SwitchStack.sw i 2 := by
  simp [headMeaning,port,headVertex,MarkedGraph.decode]

theorem port_index (φ : CNF) (i : Fin (levels φ)) : FormulaCoefficientPlan.index (port φ i) = 20*i.val+2 :=
  FormulaSwitchCursor.index φ i 2

end UnconstrainedPACDetection.FormulaClauseSwitchCursor

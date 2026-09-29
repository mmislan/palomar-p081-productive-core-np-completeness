module

public import proofs.UnconstrainedPACDetection.FormulaLinkage
public import proofs.UnconstrainedPACDetection.ListSimplePaths
public import proofs.UnconstrainedPACDetection.MarkedGraphSource

@[expose] public section

namespace UnconstrainedPACDetection.PACFormulaReduction
open Complexity.SAT FormulaWiring SwitchStack DirectedPathNormalization

instance vertexFintype (φ : CNF) : Fintype (Vertex φ) := by
  unfold Vertex Node
  infer_instance

def terminal (φ : CNF) : Bool ⊕ Bool → Vertex φ
  | .inl false => sourceP φ
  | .inl true => sourceQ φ
  | .inr false => sinkP φ
  | .inr true => sinkQ φ

theorem terminal_injective (φ : CNF) : Function.Injective (terminal φ) := by
  intro x y h
  cases x with
  | inl x =>
    cases y with
    | inl y => cases x <;> cases y <;> simp_all [terminal,sourceP,sourceQ,sw]
    | inr y => cases x <;> cases y <;> simp_all [terminal,sourceP,sourceQ,sinkP,sinkQ,sw]
  | inr x =>
    cases y with
    | inl y => cases x <;> cases y <;> simp_all [terminal,sourceP,sourceQ,sinkP,sinkQ,sw]
    | inr y => cases x <;> cases y <;> simp_all [terminal,sinkP,sinkQ,sw]

def terminals (φ : CNF) : (Bool ⊕ Bool) ↪ Vertex φ := ⟨terminal φ,terminal_injective φ⟩

theorem accepted_iff_linkage (φ : CNF) :
    (∃ p q, Accepted φ p q) ↔
      Linkage (adjacency φ) (sourceP φ) (sourceQ φ) (sinkP φ) (sinkQ φ) := by
  constructor
  · rintro ⟨p,q,h⟩
    obtain ⟨P,hP⟩ := ListSimplePaths.of_list
      (show sourceP φ ≠ sinkP φ by simp [sourceP,sinkP,sw])
      h.p_chain h.p_nodup h.p_start h.p_finish
    obtain ⟨Q,hQ⟩ := ListSimplePaths.of_list
      (show sourceQ φ ≠ sinkQ φ by simp [sourceQ,sinkQ,sw])
      h.q_chain h.q_nodup h.q_start h.q_finish
    refine ⟨P,Q,Set.disjoint_left.mpr ?_⟩
    intro x hx hy
    exact List.disjoint_left.mp h.disjoint (hP x hx) (hQ x hy)
  · rintro ⟨P,Q,hd⟩
    obtain ⟨p,ps,pt,pc,pn,pm⟩ := ListSimplePaths.to_list P
    obtain ⟨q,qs,qt,qc,qn,qm⟩ := ListSimplePaths.to_list Q
    refine ⟨p,q,⟨pc,qc,pn,qn,?_,ps,pt,qs,qt⟩⟩
    exact List.disjoint_left.mpr (fun x hx hy => Set.disjoint_left.mp hd (pm x hx) (qm x hy))

noncomputable def source (φ : CNF) :=
  DirectedLinkageSource.MarkedGraph.graphSource
    (X := Vertex φ) (adjacency φ) (terminals φ)

/-- The actual literal source has a PAC exactly when the pinned formula is satisfiable.
This is semantic correctness, not a polynomial execution theorem. -/
theorem pac_iff_sat (φ : CNF) :
    (∃ candidate, (source φ).PAC candidate) ↔ φ.Satisfiable := by
  classical
  rw [source,DirectedLinkageSource.MarkedGraph.pac_iff_marked_linkage]
  change Linkage (adjacency φ) (sourceP φ) (sourceQ φ) (sinkP φ) (sinkQ φ) ↔ _
  rw [← accepted_iff_linkage,FormulaLinkage.formula_paths_iff_sat]

end UnconstrainedPACDetection.PACFormulaReduction

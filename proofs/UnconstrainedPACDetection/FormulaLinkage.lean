module

public import proofs.UnconstrainedPACDetection.ClauseSatisfaction
public import proofs.UnconstrainedPACDetection.FormulaForward

@[expose] public section

namespace UnconstrainedPACDetection.FormulaLinkage
open Complexity.SAT FormulaWiring ClauseSatisfaction

/-- The global converse for the actual formula graph and pinned list-based
SAT semantics, with no nonemptiness or restricted-clause promise. -/
theorem accepted_implies_sat (φ : CNF) {p q : List (Vertex φ)}
    (h : Accepted φ p q) : φ.Satisfiable := by
  obtain ⟨σ,hσ⟩ := accepted_clause_truth φ h
  refine ⟨List.ofFn σ,?_⟩
  apply List.all_eq_true.mpr
  intro cl hcl
  obtain ⟨c,hc,rfl⟩ := List.mem_iff_getElem.mp hcl
  obtain ⟨l,hl,hv,hs⟩ := hσ ⟨c,hc⟩
  apply List.any_eq_true.mpr
  refine ⟨l,hl,?_⟩
  simp [Lit.eval,Assignment.get,hv,hs]

/-- The concrete formula graph accepts exactly the satisfiable pinned CNFs. -/
theorem formula_paths_iff_sat (φ : CNF) :
    (∃ p q, Accepted φ p q) ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨p,q,h⟩
    exact accepted_implies_sat φ h
  · exact FormulaForward.sat_implies_accepted φ

end UnconstrainedPACDetection.FormulaLinkage

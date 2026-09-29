module

public import proofs.UnconstrainedPACDetection.FormulaLookupExecution

@[expose] public section

namespace UnconstrainedPACDetection.FormulaLookupScan
open Complexity SAT

def blockedResult (r : Result) (v : Nat) (b : Bool) : Bool :=
  match decode r with
  | none => false
  | some (_,l) => l.var == v && l.sign != b

/-- Prepared-input boundary consumed by occurrence-dependent graph coefficients.
Input positioning, query staging and final restoration are separate caller costs. -/
theorem lookup_run (xs : List Bool) (φ : CNF) (hφ : CNF.decode? xs = some φ)
    (i : Fin (FormulaWiring.levels φ)) (c : Cfg 2 machine.Q)
    (hs : c.state = some none) (hi : c.input.HasBinarySuffix xs)
    (hq : (c.work 0).HasBinarySuffix (List.replicate i.val true))
    (hc : (c.work 1).HasBinaryPrefix []) (ho : c.output.HasBinaryPrefix []) :
    ∃ d t r, t ≤ xs.length+1 ∧ machine.reachesIn t c d ∧ machine.halted d ∧
      (d.work 0).HasBinarySuffix (List.replicate r.remaining true) ∧
      (d.work 1).HasBinaryPrefix (List.replicate r.clauses true) ∧
      d.output.HasBinaryPrefix r.raw ∧ d.input.cells = c.input.cells ∧
      decode r = FormulaWiring.lookup φ i ∧
      ∀ (v : Fin (FormulaWiring.varCount φ)) (b : Bool),
        blockedResult r v.val b = FormulaWiring.blocked φ i v b := by
  obtain ⟨d,t,ht,hd,hh,hq',hc',ho'⟩ := scan xs none i.val c [] [] hs hi hq hc ho
  have hr : decode (run none i.val xs) = FormulaWiring.lookup φ i :=
    decoded_lookup xs φ hφ i.val
  have hinput : d.input.cells = c.input.cells := by
    clear hs hi hq hc ho ht hh hq' hc' ho'
    induction hd with
    | zero => rfl
    | step hstep _ ih =>
      rw [ih]
      unfold TM.step at hstep
      split at hstep
      · contradiction
      · cases hstep
        exact Tape.move_cells _ _
  refine ⟨d,t,run none i.val xs,ht,hd,hh,hq',?_,?_,hinput,hr,?_⟩
  · simpa using hc'
  · simpa using ho'
  · intro v b
    simp only [blockedResult,hr,FormulaWiring.blocked]
    rfl

end UnconstrainedPACDetection.FormulaLookupScan

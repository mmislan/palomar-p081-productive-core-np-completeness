module

/- Local adaptation: traditional module visibility and repository import paths; mathematical declarations unchanged. See Complexitylib/UPSTREAM.md. -/
/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/


public import proofs.Complexitylib.Classes.P.Internal.NormalForm
public import proofs.Complexitylib.Models.TuringMachine.Composition.PairWithInput

@[expose] public section

/-!
# Polynomial-time pairing with the original input — proof internals
-/



namespace Complexity

/-- Internal closure of `FP` under `x ↦ pair (f x) x`. -/
theorem mem_FP_pairWithInput_internal {f : List Bool → List Bool}
    (hf : f ∈ FP) : (fun x => pair (f x) x) ∈ FP := by
  obtain ⟨k, tm, p, hcomp⟩ :=
    mem_FP_iff_computesInTime_polynomial_internal.mp hf
  let q : Polynomial ℕ :=
    Polynomial.C 5 * p + Polynomial.X + Polynomial.C 12
  apply mem_FP_iff_computesInTime_polynomial_internal.mpr
  refine ⟨TM.pairWithInputTapeCount k, TM.pairWithInputTM tm, q, ?_⟩
  have hpair := TM.pairWithInputTM_computesInTime hcomp
  change (TM.pairWithInputTM tm).ComputesInTime (fun x => pair (f x) x)
    (fun x => 5 * Polynomial.eval x p + x + 12) at hpair
  simpa [q] using hpair

end Complexity

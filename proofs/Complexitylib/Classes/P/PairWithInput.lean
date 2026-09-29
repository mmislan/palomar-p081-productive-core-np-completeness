module

/- Local adaptation: traditional module visibility and repository import paths; mathematical declarations unchanged. See Complexitylib/UPSTREAM.md. -/
/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/


public import proofs.Complexitylib.Classes.P.PairWithInput.Internal

@[expose] public section

/-!
# Polynomial-time pairing with the original input

## Main result

- `mem_FP_pairWithInput` — if `f ∈ FP`, then `x ↦ pair (f x) x` is in `FP`
-/



namespace Complexity

/-- A polynomial-time function can be evaluated and paired with its unchanged
original input in polynomial time. -/
theorem mem_FP_pairWithInput {f : List Bool → List Bool}
    (hf : f ∈ FP) : (fun x => pair (f x) x) ∈ FP :=
  mem_FP_pairWithInput_internal hf

end Complexity


module

/- Local adaptation: traditional module visibility and repository import paths; mathematical declarations unchanged. See Complexitylib/UPSTREAM.md. -/
/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/


public import proofs.Complexitylib.Classes.P.UnaryLength.Internal

@[expose] public section

/-!
# Polynomial-time unary input length

## Main result

- `unaryLength_mem_FP` — `x ↦ 1^|x|` is polynomial-time computable
-/



namespace Complexity

/-- Writing one unary mark per input bit is a polynomial-time string
function. -/
theorem unaryLength_mem_FP :
    (fun x : List Bool => List.replicate x.length true) ∈ FP :=
  unaryLength_mem_FP_internal

end Complexity


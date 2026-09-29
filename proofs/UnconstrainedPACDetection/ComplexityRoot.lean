module

public import proofs.UnconstrainedPACDetection.FormulaTotalWriter
public import proofs.UnconstrainedPACDetection.VerifierNPPolynomial
public import proofs.Complexitylib.SAT.CookLevin.Assembly

@[expose] public section

namespace UnconstrainedPACDetection
open Complexity

/-- The total binary-input reduction, including malformed SAT words. -/
theorem sat_reduction : SAT.language ≤ₚ BinaryPACVerifier.language :=
  ⟨FormulaPACEncoding.compile,FormulaTotalWriter.compile_mem_FP,
    fun xs => (FormulaPACEncoding.compile_correct xs).symm⟩

/-- Unconstrained PAC detection for literal finite reversible sources with
binary-encoded nonnegative integer complexes is NP-complete. No target or
allowed-food set is part of the input. -/
theorem complexity_root : NPComplete BinaryPACVerifier.language :=
  NPComplete.of_mem_of_reduction SAT.NPHard_language
    VerifierNPPolynomial.in_NP sat_reduction

end UnconstrainedPACDetection

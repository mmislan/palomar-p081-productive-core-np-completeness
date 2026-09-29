module

public import proofs.UnconstrainedPACDetection.VerifierNPAcceptance
public import proofs.Complexitylib.Classes.NP

@[expose] public section

namespace UnconstrainedPACDetection.VerifierNPPolynomial
open Complexity Complexity.TM
open VerifierNPMachine

noncomputable def timePolynomial : Polynomial Nat :=
  let X := Polynomial.X
  let W := 16*(X+1)^3
  (3*X+18+(4*((4*(32*((W+2)*(W+2)*(W+2)))+3)+1)+1))+1+
    ((3*W+3)+1+(26*X+84*(W+1)^2+14*W+232+256*(2*(W+1)^2+2)^3+
      100*(2*W+1)^2+22000*(X+3*W+2)^4))

theorem bound_eval (N : Nat) : bound N = timePolynomial.eval N := by
  simp [bound,VerifierNPStart.bound,VerifierNPPrepare.arithmeticTime,
    guessVerifyBound,VerifierNPGuess.bound,NTM.guessBoundedTime,evaluationBudget,
    VerifierNPBound.cap,layerBudget,opBudget,timePolynomial]

theorem polynomial_time : bound =O (· ^ timePolynomial.natDegree) :=
  BigO.of_polynomial_bound timePolynomial (fun N => le_of_eq (bound_eval N))

/-- Actual polynomial-time nondeterministic membership, with no generic
witness-machine construction premise. -/
theorem in_NP : BinaryIntegerVerifier.language ∈ NP := by
  apply Set.mem_iUnion.mpr
  exact ⟨timePolynomial.natDegree,33,machine,bound,VerifierNPAcceptance.decides,polynomial_time⟩

end UnconstrainedPACDetection.VerifierNPPolynomial

module

public import proofs.IrrRAFEnumeration.SATOutputEncoding

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource RAF

/-- Explicit rectangular CNF incidence input. The unary dimensions make the
input-size convention explicit, including unused variables and empty clauses. -/
def cnfBody {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  List.ofFn (fun k : Fin (m*(n*2)) =>
    let ix : Fin m × Fin (n*2) := finProdFinEquiv.symm k
    decide ((choiceOffset n).symm ix.2 ∈ Φ ix.1))

def cnfBits {n m : Nat} (Φ : Fin m → Finset (Choice n)) : List Bool :=
  List.replicate n true ++ [false] ++ List.replicate m true ++ [false] ++ cnfBody Φ

def decodeClauses (n m : Nat) (body : List Bool) (j : Fin m) : Finset (Choice n) :=
  Finset.univ.filter (fun x =>
    body.getD (finProdFinEquiv (j, choiceOffset n x)).val false)

theorem decodeClauses_cnfBody {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    decodeClauses n m (cnfBody Φ) = Φ := by
  funext j
  apply Finset.ext
  intro x
  simp only [decodeClauses, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [cnfBody, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp only [dite_eq_left (finProdFinEquiv (j, choiceOffset n x)).isLt]
  change (some (decide ((choiceOffset n).symm
    (finProdFinEquiv.symm (finProdFinEquiv (j, choiceOffset n x))).2 ∈
      Φ (finProdFinEquiv.symm (finProdFinEquiv (j, choiceOffset n x))).1))).getD false
        = true ↔ x ∈ Φ j
  simp only [Equiv.symm_apply_apply, Option.getD_some, decide_eq_true_eq]

theorem decodeHeader_cnfBits {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    decodeHeader (cnfBits Φ) = (n, m, cnfBody Φ) := by
  simp [cnfBits, decodeHeader, List.append_assoc, readUnary_prefix]

/-- One executable compiler on finite bitstrings; malformed inputs are padded
with false incidences. Correctness is asserted for the specified CNF encoding. -/
def compileCNF (bits : List Bool) : List Bool :=
  let parsed := decodeHeader bits
  sourceBits (decodeClauses parsed.1 parsed.2.1 parsed.2.2)

theorem compileCNF_correct {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    compileCNF (cnfBits Φ) = sourceBits Φ := by
  change (fun p : Nat × Nat × List Bool =>
    sourceBits (decodeClauses p.1 p.2.1 p.2.2)) (decodeHeader (cnfBits Φ)) = sourceBits Φ
  rw [decodeHeader_cnfBits]
  exact congrArg sourceBits (decodeClauses_cnfBody Φ)

theorem cnfBits_length {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    (cnfBits Φ).length = n+m+2+m*(n*2) := by
  simp [cnfBits, cnfBody]
  omega

/-- Polynomial output bit length for the actual uniform compiler, measured
against its explicit input bit length. This is a size bound, not a runtime bound. -/
theorem compileCNF_output_length {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    (compileCNF (cnfBits Φ)).length ≤ 500*(cnfBits Φ).length^4 := by
  rw [compileCNF_correct]
  have hsize : n+m+1 ≤ (cnfBits Φ).length := by rw [cnfBits_length]; omega
  exact (sourceBits_polynomial Φ).trans
    (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hsize 4))

theorem baseline_length_in_input_bits {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    (baselineBits n m).length ≤ 20*(cnfBits Φ).length^3 := by
  have hsize : n+m+1 ≤ (cnfBits Φ).length := by rw [cnfBits_length]; omega
  exact (baselineBits_polynomial n m).trans
    (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left hsize 3))

end IrrRAFEnumeration.SATSource

module

public import proofs.UnconstrainedPACDetection.VerifierUnaryBinary

@[expose] public section

namespace UnconstrainedPACDetection.FormulaHeaderBinaryDigits
open VerifierBinaryAdd

private theorem add_zero (xs : List Bool) : add false [] xs = xs := by
  induction xs with
  | nil => simp [add]
  | cons b xs ih => cases b <;> simp [add,digit,carry,ih]

private theorem carry_one (xs : List Bool) :
    add true [] xs = add false [true] xs := by
  cases xs with
  | nil => simp [add,digit,carry]
  | cons b xs => cases b <;> simp [add,digit,carry]

theorem increment_bits (n : Nat) : add false [true] n.bits = (n+1).bits := by
  induction n using Nat.binaryRec' with
  | zero => simp [add,digit,carry]
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    cases b with
    | false =>
      have he : Nat.bit false n+1 = 2*n+1 := by simp [Nat.bit]
      rw [he,Nat.bit1_bits]
      simp [add,digit,carry,add_zero]
    | true =>
      have he : Nat.bit true n+1 = 2*(n+1) := by simp [Nat.bit]; omega
      rw [he,Nat.bit0_bits (n+1) (by omega)]
      simpa [add,digit,carry,← carry_one] using congrArg (List.cons false) ih

/-- Repeated addition supplies the canonical bits, not only the same numerical value. -/
theorem digits_eq_bits (n : Nat) : VerifierUnaryBinary.digits n = n.bits := by
  induction n with
  | zero => rfl
  | succ n ih => rw [VerifierUnaryBinary.digits,ih,increment_bits]

end UnconstrainedPACDetection.FormulaHeaderBinaryDigits

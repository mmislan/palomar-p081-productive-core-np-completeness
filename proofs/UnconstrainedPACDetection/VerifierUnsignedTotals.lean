module

public import proofs.UnconstrainedPACDetection.IntegerFlowChecker
public import Mathlib.Data.Nat.Size

@[expose] public section

/-! Exact implementation identity: signed net-flow dot products can be
checked with two unsigned totals and one strict comparison. -/
namespace UnconstrainedPACDetection.VerifierUnsignedTotals

def positive (left right : ℕ) (flow : ℤ) : ℕ :=
  (if 0 ≤ flow then right else left) * flow.natAbs

def negative (left right : ℕ) (flow : ℤ) : ℕ :=
  (if 0 ≤ flow then left else right) * flow.natAbs

theorem term_identity (left right : ℕ) (flow : ℤ) :
    ((right : ℤ) - left) * flow =
      (positive left right flow : ℤ) - negative left right flow := by
  by_cases h : 0 ≤ flow
  · simp [positive, negative, h, abs_of_nonneg h]
    ring
  · have hn : flow < 0 := lt_of_not_ge h
    simp [positive, negative, h, abs_of_neg hn]
    ring

variable {Entity Reaction : Type*} [Fintype Reaction]

def positiveTotal (s : ReversibleSource Entity Reaction) (w : Reaction → ℤ) (x : Entity) : ℕ :=
  ∑ r, positive (s.left r x) (s.right r x) (w r)

def negativeTotal (s : ReversibleSource Entity Reaction) (w : Reaction → ℤ) (x : Entity) : ℕ :=
  ∑ r, negative (s.left r x) (s.right r x) (w r)

theorem dot_identity (s : ReversibleSource Entity Reaction) (w : Reaction → ℤ) (x : Entity) :
    ∑ r, s.netInt r x * w r =
      (positiveTotal s w x : ℤ) - negativeTotal s w x := by
  simp only [ReversibleSource.netInt, term_identity, positiveTotal, negativeTotal,
    Nat.cast_sum, Finset.sum_sub_distrib]

theorem productive_iff_compare (s : ReversibleSource Entity Reaction)
    (w : Reaction → ℤ) (x : Entity) :
    0 < ∑ r, s.netInt r x * w r ↔ negativeTotal s w x < positiveTotal s w x := by
  rw [dot_identity, sub_pos]
  exact_mod_cast Iff.rfl

theorem checker_iff [Fintype Entity] [DecidableEq Entity] [DecidableEq Reaction]
    (s : ReversibleSource Entity Reaction) (X : Finset Entity) (w : Reaction → ℤ) :
    s.checkIntegerFlow X w = true ↔
      X.Nonempty ∧
      (∀ r, w r = 0 ∨ ((∃ x ∈ X, 0 < s.left r x) ∧ ∃ x ∈ X, 0 < s.right r x)) ∧
      ∀ x ∈ X, negativeTotal s w x < positiveTotal s w x := by
  simp only [ReversibleSource.checkIntegerFlow, decide_eq_true_eq, productive_iff_compare]

private theorem sum_size (terms : Reaction → ℕ) (k : ℕ)
    (h : ∀ r, terms r ≤ 2 ^ k) : (∑ r, terms r).size ≤ Fintype.card Reaction + k := by
  apply Nat.size_le.mpr
  calc
    ∑ r, terms r ≤ ∑ _r : Reaction, 2 ^ k := Finset.sum_le_sum (fun r _ => h r)
    _ = Fintype.card Reaction * 2 ^ k := by simp
    _ < 2 ^ Fintype.card Reaction * 2 ^ k :=
      Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (by positivity)
    _ = 2 ^ (Fintype.card Reaction + k) := (Nat.pow_add _ _ _).symm

/-- Both unsigned accumulators have polynomial bit length. The count bound
is deliberately loose: logarithmic count bits would also suffice. -/
theorem totals_size (s : ReversibleSource Entity Reaction) (w : Reaction → ℤ)
    (x : Entity) (b f : ℕ)
    (hl : ∀ r, s.left r x ≤ 2 ^ b) (hr : ∀ r, s.right r x ≤ 2 ^ b)
    (hw : ∀ r, (w r).natAbs ≤ 2 ^ f) :
    (positiveTotal s w x).size ≤ Fintype.card Reaction + (b + f) ∧
    (negativeTotal s w x).size ≤ Fintype.card Reaction + (b + f) := by
  constructor
  · apply sum_size
    intro r
    unfold positive
    rw [Nat.pow_add]
    apply Nat.mul_le_mul _ (hw r)
    split_ifs <;> first | exact hr r | exact hl r
  · apply sum_size
    intro r
    unfold negative
    rw [Nat.pow_add]
    apply Nat.mul_le_mul _ (hw r)
    split_ifs <;> first | exact hl r | exact hr r

end UnconstrainedPACDetection.VerifierUnsignedTotals


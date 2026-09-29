module

public import proofs.MinRAFApprox.EncodingSize

@[expose] public section

namespace MinRAFApprox.SetCoverSource

/-- Affine optimum value induced by a cover of cardinality `a`. -/
def sourceValue (m M a : Nat) : Nat := m + M * a

/-- A certified factor-`c` lower estimate of an optimum value. -/
def IsLowerEstimate (c optimum value : Nat) : Prop :=
  value ≤ optimum ∧ optimum ≤ c * value

/-- A certified factor-`c` upper estimate of an optimum value. -/
def IsUpperEstimate (c optimum value : Nat) : Prop :=
  optimum ≤ value ∧ value ≤ c * optimum

/-- A two-sided multiplicative estimate, expressed without division. -/
def IsSymmetricEstimate (c optimum value : Nat) : Prop :=
  optimum ≤ c * value ∧ value ≤ c * optimum

/-- The paper's linear gap condition is exactly sufficient to separate the
affine YES and NO source values. -/
theorem linear_gap_condition
    {m M a c κ : Nat} (hc : 1 ≤ c) (hκ : c ≤ κ)
    (hgap : m * (c - 1) < M * a * (κ - c)) :
    c * sourceValue m M a < sourceValue m M (κ * a) := by
  have hcsub : c - 1 + 1 = c := Nat.sub_add_cancel hc
  have hκsub : κ - c + c = κ := Nat.sub_add_cancel hκ
  rw [← hκsub, ← hcsub] at hgap ⊢
  simp [sourceValue] at hgap ⊢
  nlinarith

/-- The squared gap condition needed for a symmetric estimate. -/
theorem squared_gap_condition
    {m M a c κ : Nat} (hc : 1 ≤ c) (hcκ : c * c ≤ κ)
    (hgap : m * (c * c - 1) < M * a * (κ - c * c)) :
    c * c * sourceValue m M a < sourceValue m M (κ * a) := by
  have hccpos : 1 ≤ c * c := by nlinarith
  have hccsub : c * c - 1 + 1 = c * c := Nat.sub_add_cancel hccpos
  have hκsub : κ - c * c + c * c = κ := Nat.sub_add_cancel hcκ
  rw [← hκsub, ← hccsub] at hgap ⊢
  simp [sourceValue] at hgap ⊢
  nlinarith

/-- Under a separated affine gap, every valid lower estimate for a NO value
lies strictly above the largest possible lower estimate for the YES value. -/
theorem lower_estimate_gap_separation
    {m M a c κ Lno : Nat}
    (hgap : c * sourceValue m M a < sourceValue m M (κ * a))
    (hno : IsLowerEstimate c (sourceValue m M (κ * a)) Lno) :
    sourceValue m M a < Lno := by
  rcases hno with ⟨_hbelow, habove⟩
  by_contra h
  have hL : Lno ≤ sourceValue m M a := Nat.le_of_not_gt h
  have hmul := Nat.mul_le_mul_left c hL
  omega

/-- Under the same gap, every valid upper estimate for a YES value lies below
the smallest possible upper estimate for the NO value. -/
theorem upper_estimate_gap_separation
    {m M a c κ Uyes : Nat}
    (hgap : c * sourceValue m M a < sourceValue m M (κ * a))
    (hyes : IsUpperEstimate c (sourceValue m M a) Uyes) :
    Uyes < sourceValue m M (κ * a) := by
  exact lt_of_le_of_lt hyes.2 hgap

/-- A symmetric factor-`c` estimate needs a `c^2` gap: every NO estimate is
then above every YES-side threshold `c * OPT_yes`. -/
theorem symmetric_estimate_gap_separation
    {m M a c κ Vno : Nat}
    (hgap : c * c * sourceValue m M a < sourceValue m M (κ * a))
    (hno : IsSymmetricEstimate c (sourceValue m M (κ * a)) Vno) :
    c * sourceValue m M a < Vno := by
  rcases hno with ⟨habove, _hbelow⟩
  by_contra h
  have hV : Vno ≤ c * sourceValue m M a := Nat.le_of_not_gt h
  have hmul := Nat.mul_le_mul_left c hV
  nlinarith

/-- A single number cannot satisfy the lower-estimate guarantees on both
sides of a linearly separated gap. -/
theorem no_common_lower_estimate
    {m M a c κ L : Nat}
    (hgap : c * sourceValue m M a < sourceValue m M (κ * a))
    (hyes : IsLowerEstimate c (sourceValue m M a) L)
    (hno : IsLowerEstimate c (sourceValue m M (κ * a)) L) : False := by
  exact (Nat.not_lt_of_ge hyes.1) (lower_estimate_gap_separation hgap hno)

/-- A single number cannot satisfy the upper-estimate guarantees on both
sides of a linearly separated gap. -/
theorem no_common_upper_estimate
    {m M a c κ U : Nat}
    (hgap : c * sourceValue m M a < sourceValue m M (κ * a))
    (hyes : IsUpperEstimate c (sourceValue m M a) U)
    (hno : IsUpperEstimate c (sourceValue m M (κ * a)) U) : False := by
  exact (Nat.not_lt_of_ge hno.1) (upper_estimate_gap_separation hgap hyes)

/-- A single number cannot satisfy symmetric guarantees on both sides of a
quadratically separated gap. -/
theorem no_common_symmetric_estimate
    {m M a c κ V : Nat}
    (hgap : c * c * sourceValue m M a < sourceValue m M (κ * a))
    (hyes : IsSymmetricEstimate c (sourceValue m M a) V)
    (hno : IsSymmetricEstimate c (sourceValue m M (κ * a)) V) : False := by
  have hbelow : V ≤ c * sourceValue m M a := hyes.2
  exact (Nat.not_lt_of_ge hbelow)
    (symmetric_estimate_gap_separation hgap hno)

end MinRAFApprox.SetCoverSource

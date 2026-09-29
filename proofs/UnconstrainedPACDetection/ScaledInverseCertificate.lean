module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Real.Basic

@[expose] public section

/-! Exact integer certificates for the square-minor verifier. Runtime and
certificate encoding bounds are separate obligations. -/

namespace UnconstrainedPACDetection.ScaledInverseCertificate

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

def Accepts (A : Matrix n n ℤ) (d : ℤ) (B : Matrix n n ℤ) : Prop :=
  d ≠ 0 ∧ A * B = d • (1 : Matrix n n ℤ)

theorem det_ne_zero_of_accepts {A B : Matrix n n ℤ} {d : ℤ}
    (h : Accepts A d B) : A.det ≠ 0 := by
  have heq := congrArg Matrix.det h.2
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at heq
  intro hz
  rw [hz, zero_mul] at heq
  exact (pow_ne_zero _ h.1) heq.symm

theorem exists_certificate_iff (A : Matrix n n ℤ) :
    (∃ d B, Accepts A d B) ↔ A.det ≠ 0 := by
  constructor
  · rintro ⟨d, B, h⟩
    exact det_ne_zero_of_accepts h
  · intro h
    exact ⟨A.det, A.adjugate, h, Matrix.mul_adjugate A⟩

theorem real_rows_iff_certificate (A : Matrix n n ℤ) :
    LinearIndependent ℝ (fun i j => (A i j : ℝ)) ↔
      ∃ d B, Accepts A d B := by
  rw [exists_certificate_iff]
  have hcast : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    (Int.castRingHom ℝ).map_det A |>.symm
  change LinearIndependent ℝ (A.map (Int.castRingHom ℝ)).row ↔ _
  rw [Matrix.linearIndependent_rows_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    isUnit_iff_ne_zero, hcast]
  exact Int.cast_ne_zero

end UnconstrainedPACDetection.ScaledInverseCertificate

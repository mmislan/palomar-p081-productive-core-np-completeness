module

public import proofs.UnconstrainedPACDetection.VerifierBinaryAdd

@[expose] public section

/-! The bit-bounded multiplication recurrence consumed by the planned machine
loop. `additionWork` counts only invocations of the proved adder; copying,
rewinding and loop-control execution remain separate machine obligations. -/
namespace UnconstrainedPACDetection.VerifierBinaryProduct

def step (xs : List Bool) (b : Bool) (acc : List Bool) : List Bool :=
  if b then VerifierBinaryAdd.add false xs (false :: acc) else false :: acc

def multiply (xs : List Bool) : List Bool → List Bool
  | [] => []
  | b :: ys => step xs b (multiply xs ys)

theorem step_value (xs acc : List Bool) (b : Bool) :
    BinaryFields.readNat (step xs b acc) =
      2 * BinaryFields.readNat acc + b.toNat * BinaryFields.readNat xs := by
  cases b
  · simp [step, BinaryFields.readNat, Nat.bit]
  · simp [step, VerifierBinaryAdd.add_value, BinaryFields.readNat, Nat.bit]
    omega

theorem multiply_value (xs ys : List Bool) :
    BinaryFields.readNat (multiply xs ys) = BinaryFields.readNat xs * BinaryFields.readNat ys := by
  induction ys with
  | nil => simp [multiply, BinaryFields.readNat]
  | cons b ys ih =>
    simp only [multiply, step_value, ih]
    cases b <;> simp [BinaryFields.readNat, Nat.bit] <;> ring

theorem step_length (xs acc : List Bool) (b : Bool) :
    (step xs b acc).length ≤ max xs.length acc.length + 2 := by
  cases b with
  | false => simp [step]; omega
  | true =>
    have h := VerifierBinaryAdd.add_length false xs (false :: acc)
    simp only [List.length_cons] at h
    simpa only [step, ↓reduceIte] using h.trans (by omega)

theorem multiply_length (xs ys : List Bool) :
    (multiply xs ys).length ≤ xs.length + 2 * ys.length := by
  induction ys with
  | nil => simp [multiply]
  | cons b ys ih =>
    have h := step_length xs (multiply xs ys) b
    simp only [multiply, List.length_cons]
    omega

/-- Same straight-line Horner program: the uniform machine can read multiplier
bits right-to-left. This is an equality of programs, not a machine-cost theorem. -/
theorem multiply_foldr (xs ys : List Bool) : multiply xs ys = ys.foldr (step xs) [] := by
  induction ys with
  | nil => rfl
  | cons b ys ih => simp [multiply, ih]

def additionWork (xs : List Bool) : List Bool → ℕ
  | [] => 0
  | b :: ys => additionWork xs ys +
      if b then max xs.length (multiply xs ys).length.succ + 1 else 0

/-- Sum of the exact costs of adder calls. The additional data movement and
control costs must still be proved for one uniform finite machine. -/
theorem additionWork_bound (xs ys : List Bool) :
    additionWork xs ys ≤ ys.length * (xs.length + 2 * ys.length + 2) := by
  induction ys with
  | nil => simp [additionWork]
  | cons b ys ih =>
    have hsize := multiply_length xs ys
    have hmax : max xs.length (multiply xs ys).length.succ + 1 ≤
        xs.length + 2 * ys.length + 2 := by omega
    have hstep : additionWork xs (b :: ys) ≤
        ys.length * (xs.length + 2 * ys.length + 2) + (xs.length + 2 * ys.length + 2) := by
      cases b <;> simp only [additionWork, Bool.false_eq_true, ↓reduceIte]
      · omega
      · omega
    simp only [List.length_cons]
    nlinarith

end UnconstrainedPACDetection.VerifierBinaryProduct

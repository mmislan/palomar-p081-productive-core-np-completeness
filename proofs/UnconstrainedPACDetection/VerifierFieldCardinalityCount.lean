module

public import proofs.UnconstrainedPACDetection.VerifierRawDimensions
public import proofs.Complexitylib.Models.TuringMachine.Registers.Horner

@[expose] public section

namespace UnconstrainedPACDetection.VerifierFieldCardinalityCount
open Complexity Complexity.TM

def frame (base : Fin 11 → Tape) (v : ℕ) : Fin 11 → Tape := Function.update base 10 (regTape v)
def multiply : TM 11 := mulAddIntoTM 5 8 10
def increment : TM 11 := incRegTM 10
def machine : TM 11 := seqTM multiply (seqTM multiply (seqTM increment increment))

theorem frame_parked (base : Fin 11 → Tape) (hp : ∀ j, Parked (base j)) (v : ℕ) :
    ∀ j, Parked (frame base v j) := by
  intro j; by_cases hj : j = 10
  · subst j; exact parked_regTape v
  · simpa only [frame,Function.update_of_ne hj] using hp j

theorem mul_hoare (m n d M : ℕ) (inp₀ : Tape) (base : Fin 11 → Tape) (ys : List Bool)
    (hi : Parked inp₀) (hp : ∀ j, Parked (base j))
    (h5 : base 5 = regTape m) (h8 : base 8 = regTape n)
    (hm : m ≤ M) (hn : n ≤ M) (hd : d+m*n ≤ M) : multiply.HoareTime
    (EmitPred inp₀ (frame base d) ys) (EmitPred inp₀ (frame base (d+m*n)) ys) (opBudget M) := by
  have h := mulAddIntoTM_hoareTime (5 : Fin 11) 8 10 (by decide) (by decide) (by decide)
    m n d inp₀ (frame base d) ys hi (fun j _ => frame_parked base hp d j)
    (by exact h5) (by exact h8) (by rfl)
  have h' := h.mono_bound (mulAddIntoTM_le_opBudget hm hn hd)
  simpa only [multiply, frame,Function.update_idem] using h'

theorem inc_hoare (d M : ℕ) (inp₀ : Tape) (base : Fin 11 → Tape) (ys : List Bool)
    (hi : Parked inp₀) (hp : ∀ j, Parked (base j)) (hd : d ≤ M) : increment.HoareTime
    (EmitPred inp₀ (frame base d) ys) (EmitPred inp₀ (frame base (d+1)) ys) (opBudget M) := by
  have h := incRegTM_hoareTime (10 : Fin 11) d inp₀ (frame base d) ys hi
    (fun j _ => frame_parked base hp d j) (by rfl)
  have h' := h.mono_bound (incRegTM_le_opBudget hd)
  simpa only [increment, frame,Function.update_idem] using h'

theorem validation_hoare (m n L : ℕ) (inp₀ : Tape) (base : Fin 11 → Tape) (ys : List Bool)
    (hi : Parked inp₀) (hp : ∀ j, Parked (base j))
    (h5 : base 5 = regTape m) (h8 : base 8 = regTape n) (h10 : base 10 = regTape 0)
    (hm : m ≤ L) (hn : n ≤ L) : machine.HoareTime
    (EmitPred inp₀ base ys) (EmitPred inp₀ (frame base (2*m*n+2)) ys)
    (4*opBudget (2*(L+1)^2)+3) := by
  let M := 2*(L+1)^2
  have hmn : m*n ≤ L*L := Nat.mul_le_mul hm hn
  have hmM : m ≤ M := by dsimp [M]; nlinarith
  have hnM : n ≤ M := by dsimp [M]; nlinarith
  have hprod : m*n+m*n+2 ≤ M := by dsimp [M]; nlinarith
  have h0 := mul_hoare m n 0 M inp₀ base ys hi hp h5 h8 hmM hnM (by omega)
  have h1 := mul_hoare m n (m*n) M inp₀ base ys hi hp h5 h8 hmM hnM (by omega)
  have h2 := inc_hoare (m*n+m*n) M inp₀ base ys hi hp (by omega)
  have h3 := inc_hoare (m*n+m*n+1) M inp₀ base ys hi hp (by omega)
  have hs2 := seqTM_hoareTime _ _ h2 (emitPred_transition hi (frame_parked base hp _) ys) h3
  have hs1 := seqTM_hoareTime _ _ h1 (emitPred_transition hi (frame_parked base hp _) ys) hs2
  have hs0 := seqTM_hoareTime _ _ h0 (emitPred_transition hi (frame_parked base hp _) ys)
    (by simpa only [Nat.zero_add] using hs1)
  have hstart : frame base 0 = base := by
    rw [frame,←h10,Function.update_eq_self]
  have hend : m*n+m*n+1+1 = 2*m*n+2 := by ring
  simpa only [machine,hstart,Nat.zero_add,hend,M,show opBudget (2*(L+1)^2) + 1 +
    (opBudget (2*(L+1)^2) + 1 + (opBudget (2*(L+1)^2) + 1 + opBudget (2*(L+1)^2))) =
    4*opBudget (2*(L+1)^2)+3 by omega] using hs0

end UnconstrainedPACDetection.VerifierFieldCardinalityCount

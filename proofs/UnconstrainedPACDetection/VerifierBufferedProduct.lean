module

public import proofs.UnconstrainedPACDetection.VerifierProductBoundary
public import proofs.Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget

@[expose] public section

/-! Actual buffered multiplication: work3 supplies the virtual input while the
real parser cursor remains parked. Work0 is the other operand, work1 the result. -/
namespace UnconstrainedPACDetection.VerifierBufferedProduct
open Complexity
open Complexity.TM

abbrev sourceMachine := VerifierProductMachine.machine
def machine : TM 4 := retargetInput sourceMachine

theorem retarget_run {t : ℕ} {c d : Cfg 3 sourceMachine.Q}
    (h : sourceMachine.reachesIn t c d) (hi : c.input.StartInvariant)
    (realInput : Tape) (hr : realInput.read ≠ .start) :
    machine.reachesIn t (retargetWrap sourceMachine realInput c)
      (retargetWrap sourceMachine realInput d) := by
  have hidle : realInput.move (idleDir realInput.read) = realInput := by
    simp [idleDir, hr, Tape.move]
  induction h with
  | zero => exact .zero
  | step hs _ ih =>
    have hc := input_cells_eq_of_step hs
    have hi' : _ := And.intro (hc ▸ hi.1) (fun j hj => hc ▸ hi.2 j hj)
    have step := retargetInput_step_commute sourceMachine hs realInput hi
    rw [hidle] at step
    exact .step step (ih hi')

/-- Both operands are actual prepared work tapes. The parser's input cursor is
preserved exactly, and the same polynomial bound charges the retargeted run. -/
theorem multiplication_run (xs ys : List Bool) (c : Cfg 4 machine.Q)
    (hq : c.state = machine.qstart)
    (hx : (c.work 3).HasBinaryString xs) (hi : (c.work 3).StartInvariant)
    (hy : (c.work 0).HasBinaryString ys) (hm : (c.work 0).StartInvariant)
    (ha : c.work 1 = (Tape.init []).move .right)
    (ht : c.work 2 = (Tape.init []).move .right)
    (hr : c.input.read ≠ .start) (hout : c.output.read ≠ .start) :
    ∃ t d, t ≤ ys.length + 2 + ys.length * (10*xs.length + 20*ys.length + 30) ∧
      machine.reachesIn t c d ∧ machine.halted d ∧
      (d.work 1).HasBinaryString (VerifierBinaryProduct.multiply xs ys) ∧
      (d.work 1).StartInvariant ∧ d.work 3 = c.work 3 ∧ d.work 0 = c.work 0 ∧
      d.work 2 = (Tape.init []).move .right ∧ d.input = c.input ∧ d.output = c.output := by
  let s : Cfg 3 sourceMachine.Q :=
    { state := c.state, input := c.work 3, work := ![c.work 0, c.work 1, c.work 2], output := c.output }
  have hembed : retargetWrap sourceMachine c.input s = c := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> simp [s, retargetWrap]
    · rfl
  obtain ⟨t, d, hb, hd, hh, hp, hs, hinput, hmult, htemp, ho⟩ :=
    VerifierProductMachine.multiplication_run xs ys s hq hx hi hy hm ha ht hout
  refine ⟨t, retargetWrap sourceMachine c.input d, hb, ?_, hh, ?_, ?_, ?_, ?_, ?_, rfl, ho⟩
  · simpa only [hembed] using retarget_run hd hi c.input hr
  · simpa [retargetWrap] using hp
  · simpa [retargetWrap] using hs
  · simpa [retargetWrap] using hinput
  · simpa [retargetWrap, s] using hmult
  · simpa [retargetWrap] using htemp

def wordTape (xs : List Bool) : Tape := (Tape.init (xs.map Γ.ofBool)).move .right

def preparedWork (xs ys : List Bool) : Fin 4 → Tape :=
  ![wordTape ys, wordTape [], wordTape [], wordTape xs]

def finishedWork (xs ys : List Bool) : Fin 4 → Tape :=
  ![wordTape ys, wordTape (VerifierBinaryProduct.multiply xs ys), wordTape [], wordTape xs]

/-- Directly composable execution contract; all work-tape contents and heads
are specified, and both real caller tapes remain exactly unchanged. -/
theorem prepared_hoare (xs ys : List Bool) (inp₀ out₀ : Tape)
    (hin : inp₀.read ≠ .start) (hout : out₀.read ≠ .start) :
    machine.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = preparedWork xs ys ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧ work = finishedWork xs ys ∧ out = out₀)
      (ys.length + 2 + ys.length * (10*xs.length + 20*ys.length + 30)) := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  let c : Cfg 4 machine.Q :=
    ⟨machine.qstart, inp, preparedWork xs ys, out⟩
  obtain ⟨t, d, hb, hd, hh, hp, hs, hx, hy, ht, hi, ho⟩ :=
    multiplication_run xs ys c rfl
      (Tape.init_move_right_hasBinaryString xs) ((Tape.StartInvariant.init_ofBool xs).move .right)
      (Tape.init_move_right_hasBinaryString ys) ((Tape.StartInvariant.init_ofBool ys).move .right)
      rfl rfl hin hout
  have hprod : d.work 1 = wordTape (VerifierBinaryProduct.multiply xs ys) :=
    Tape.eq_init_move_right_of_hasBinaryString hp hs.1
  refine ⟨d, t, hb, hd, hh, hi, ?_, ho⟩
  funext j
  fin_cases j
  · exact hy
  · exact hprod
  · exact ht
  · exact hx

end UnconstrainedPACDetection.VerifierBufferedProduct

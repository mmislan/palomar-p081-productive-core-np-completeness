module

public import proofs.UnconstrainedPACDetection.VerifierAccumulateBoundary
public import proofs.Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget

@[expose] public section

/-! In-place work-tape accumulation with the real parser cursor preserved. -/
namespace UnconstrainedPACDetection.VerifierBufferedAccumulate
open Complexity
open Complexity.TM

abbrev sourceMachine := VerifierAccumulate.machine
def machine : TM 2 := retargetInput sourceMachine

theorem retarget_run {t : ℕ} {c d : Cfg 1 sourceMachine.Q}
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

/-- Total on work0, term on work1: the total is overwritten and both work
heads return to one, while the term and real caller tapes are unchanged. -/
theorem accumulation_run (xs ys : List Bool) (c : Cfg 2 machine.Q)
    (hq : c.state = machine.qstart)
    (hx : (c.work 1).HasBinaryString xs) (hi : (c.work 1).StartInvariant)
    (hy : (c.work 0).HasBinaryString ys) (hz : (c.work 0).cells 0 = .start)
    (hr : c.input.read ≠ .start) (hout : c.output.read ≠ .start) :
    ∃ d, machine.reachesIn
        (max xs.length ys.length + xs.length + (VerifierBinaryAdd.add false xs ys).length + 5) c d ∧
      machine.halted d ∧ (d.work 0).HasBinaryString (VerifierBinaryAdd.add false xs ys) ∧
      (d.work 0).cells 0 = .start ∧ d.work 1 = c.work 1 ∧ d.input = c.input ∧ d.output = c.output := by
  let s : Cfg 1 sourceMachine.Q :=
    ⟨c.state, c.work 1, fun _ => c.work 0, c.output⟩
  have hembed : retargetWrap sourceMachine c.input s = c := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> simp [s, retargetWrap]
    · rfl
  obtain ⟨d, hd, hh, hp, hz', hinput, ho⟩ :=
    VerifierAccumulate.accumulation_run xs ys s hq hx hi hy hz hout
  refine ⟨retargetWrap sourceMachine c.input d, ?_, hh, ?_, ?_, ?_, rfl, ho⟩
  · simpa only [hembed] using retarget_run hd hi c.input hr
  · simpa [retargetWrap] using hp
  · simpa [retargetWrap] using hz'
  · simpa [retargetWrap] using hinput

theorem prepared_hoare (xs ys : List Bool) (inp₀ out₀ : Tape)
    (hin : inp₀.read ≠ .start) (hout : out₀.read ≠ .start) :
    machine.HoareTime
      (fun inp work out => inp = inp₀ ∧
        work 0 = (Tape.init (ys.map Γ.ofBool)).move .right ∧
        work 1 = (Tape.init (xs.map Γ.ofBool)).move .right ∧ out = out₀)
      (fun inp work out => inp = inp₀ ∧
        work 0 = (Tape.init ((VerifierBinaryAdd.add false xs ys).map Γ.ofBool)).move .right ∧
        work 1 = (Tape.init (xs.map Γ.ofBool)).move .right ∧ out = out₀)
      (xs.length + 2*max xs.length ys.length + 6) := by
  rintro inp work out ⟨rfl, hy, hx, rfl⟩
  let c : Cfg 2 machine.Q := ⟨machine.qstart, inp, work, out⟩
  obtain ⟨d, hd, hh, hp, hz, ht, hi, ho⟩ := accumulation_run xs ys c rfl
    (by change (work 1).HasBinaryString xs; rw [hx]; exact Tape.init_move_right_hasBinaryString xs)
    (by change (work 1).StartInvariant; rw [hx]; exact (Tape.StartInvariant.init_ofBool xs).move .right)
    (by change (work 0).HasBinaryString ys; rw [hy]; exact Tape.init_move_right_hasBinaryString ys)
    (by change (work 0).cells 0 = .start; rw [hy]; rfl) hin hout
  refine ⟨d, _, ?_, hd, hh, hi, Tape.eq_init_move_right_of_hasBinaryString hp hz, ht.trans hx, ho⟩
  have h := VerifierBinaryAdd.add_length false xs ys
  omega

end UnconstrainedPACDetection.VerifierBufferedAccumulate

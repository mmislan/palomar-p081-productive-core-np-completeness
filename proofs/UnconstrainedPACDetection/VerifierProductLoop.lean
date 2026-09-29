module

public import proofs.UnconstrainedPACDetection.VerifierProductPrepare

@[expose] public section

/-! The fixed multiplier's phase1 branches: halt at marker or emit shift zero. -/
namespace UnconstrainedPACDetection.VerifierProductMachine
open Complexity
open Complexity.TM

theorem loop_enter_step (b : Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (1, false, false)) (hm : (c.work 0).read = Γ.ofBool b)
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (ha : (c.work 1).read ≠ .start) (ht : (c.work 2).read ≠ .start) :
    machine.step c = some { c with
      state := (2, b, false),
      work := ![c.work 0, c.work 1, (c.work 2).writeAndMove .zero .right] } := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  have hmOff : (c.work 0).read ≠ .start := by rw [hm]; exact Γ.ofBool_ne_start b
  cases b <;> simp only [TM.step, hn, ↓reduceIte]
  all_goals
    have keep := write_readBack (c.work 0) hmOff
    simp only [hm, Γ.ofBool] at keep
    simp only [machine, hq, control, markerDir, hin, hm, VerifierBinaryAdd.bit]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [ha, ht, hm, Γ.ofBool, Tape.move]
      all_goals
        first
        | exact keep
        | exact write_readBack _ ha
    · exact transitionTape_eq_self hout

theorem loop_halt_step (c : Cfg 3 machine.Q)
    (hq : c.state = (1, false, false)) (hh : (c.work 0).head = 0)
    (hm : (c.work 0).StartInvariant)
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (ha : (c.work 1).read ≠ .start) (ht : (c.work 2).read ≠ .start) :
    machine.step c = some (replaceWork c (9, false, false) 0 ((c.work 0).move .right)) := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  have hr : (c.work 0).read = .start := by change (c.work 0).cells _ = .start; rw [hh]; exact hm.1
  simp only [TM.step, hn, ↓reduceIte]
  simp only [machine, hq, control, markerDir, hin, hr, ↓reduceIte]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    fin_cases j
    · simp [replaceWork, hr, Tape.writeAndMove, Tape.move, Tape.write, hh]
    · change (c.work 1).writeAndMove (readBackWrite (c.work 1).read).toΓ
        (if (c.work 1).read = .start then .right else .stay) = c.work 1
      rw [ite_eq_right ha]
      exact writeAndMove_readBack _ ha .stay
    · change (c.work 2).writeAndMove (readBackWrite (c.work 2).read).toΓ
        (if (c.work 2).read = .start then .right else .stay) = c.work 2
      rw [ite_eq_right ht]
      exact writeAndMove_readBack _ ht .stay
  · exact transitionTape_eq_self hout

end UnconstrainedPACDetection.VerifierProductMachine

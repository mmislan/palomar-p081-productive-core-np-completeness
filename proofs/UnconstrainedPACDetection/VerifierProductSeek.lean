module

public import proofs.UnconstrainedPACDetection.VerifierProductPhases

@[expose] public section

/-! Actual phase0 execution, preserving the original multiplier word. -/
namespace UnconstrainedPACDetection.VerifierProductMachine
open Complexity
open Complexity.TM

theorem seek_step (c : Cfg 3 machine.Q) (hq : c.state = (0, false, false))
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hw : ∀ j, (c.work j).read ≠ .start) :
    machine.step c = some (replaceWork c
      (if (c.work 0).read = .blank then (1, false, false) else (0, false, false)) 0
      ((c.work 0).move (if (c.work 0).read = .blank then .left else .right))) := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  by_cases hb : (c.work 0).read = .blank
  all_goals
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, control, markerDir, hin, hb, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [replaceWork, hw, Tape.move]
      all_goals
        first
        | exact write_readBack _ (hw _)
        | exact ⟨congrArg (fun t : Tape => t.head - 1) (write_readBack (c.work 0) (hw 0)),
            congrArg Tape.cells (write_readBack (c.work 0) (hw 0))⟩
        | exact ⟨congrArg Tape.head (write_readBack (c.work 0) (hw 0)),
            congrArg Tape.cells (write_readBack (c.work 0) (hw 0))⟩
    · exact transitionTape_eq_self hout

/-- Seek to the terminator and return one cell left in exactly n+1 steps.
For an empty word initially at head1, the returned head is the start marker. -/
theorem seek_run (xs : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (0, false, false))
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hw : ∀ j, j ≠ 0 → (c.work j).read ≠ .start)
    (hx : (c.work 0).HasBinarySuffix xs) :
    ∃ d, machine.reachesIn (xs.length+1) c d ∧ d.state = (1, false, false) ∧
      (d.work 0).head = (c.work 0).head + xs.length - 1 ∧
      (d.work 0).cells = (c.work 0).cells ∧ d.input = c.input ∧ d.output = c.output ∧
      ∀ j, j ≠ 0 → d.work j = c.work j := by
  have allw : ∀ j, (c.work j).read ≠ .start := by
    intro j
    by_cases hj : j = 0
    · simpa only [hj] using hx.read_ne_start
    · exact hw j hj
  induction xs generalizing c with
  | nil =>
    have hs := seek_step c hq hin hout allw
    simp only [hx.read_nil, ↓reduceIte] at hs
    refine ⟨_, .step hs .zero, rfl, ?_, rfl, rfl, rfl, ?_⟩
    · simp [replaceWork, Tape.move]
    · intro j hj; simp [replaceWork, hj]
  | cons b xs ih =>
    let s := replaceWork c (0, false, false) 0 ((c.work 0).move .right)
    have hb : (c.work 0).read ≠ .blank := by rw [hx.read_cons]; cases b <;> decide
    have hs : machine.step c = some s := by
      simpa only [hb, ↓reduceIte] using seek_step c hq hin hout allw
    have hxs : (s.work 0).HasBinarySuffix xs := by
      simpa only [s, replaceWork, Function.update_self] using hx.move_right_cons
    have hws : ∀ j, j ≠ 0 → (s.work j).read ≠ .start := by
      intro j hj; simpa [s, replaceWork, hj] using hw j hj
    have aws : ∀ j, (s.work j).read ≠ .start := by
      intro j
      by_cases hj : j = 0
      · simpa only [hj] using hxs.read_ne_start
      · exact hws j hj
    obtain ⟨d, hd, hqd, hhd, hcd, hid, hod, hwd⟩ := ih s rfl hin hout hws hxs aws
    refine ⟨d, .step hs hd, hqd, ?_, ?_, hid, hod, ?_⟩
    · simp only [s, replaceWork, Function.update_self, Tape.move] at hhd
      simp only [List.length_cons]
      omega
    · simpa only [s, replaceWork, Function.update_self, Tape.move] using hcd
    · intro j hj; simpa [s, replaceWork, hj] using hwd j hj

end UnconstrainedPACDetection.VerifierProductMachine

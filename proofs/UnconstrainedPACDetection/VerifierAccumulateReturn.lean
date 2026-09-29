module

public import proofs.UnconstrainedPACDetection.VerifierAccumulateScan

@[expose] public section

/-! Actual rewinds complete the reusable in-place accumulator. -/
namespace UnconstrainedPACDetection.VerifierAccumulate
open Complexity
open Complexity.TM

theorem rewind_input_step (c : Cfg 1 machine.Q) (hq : c.state = (1,false))
    (hw : (c.work 0).read ≠ .start) (hout : c.output.read ≠ .start)
    (hi : c.input.StartInvariant) :
    machine.step c = some { c with
      state := if c.input.head = 0 then (2,false) else (1,false),
      input := c.input.move (if c.input.head = 0 then .right else .left) } := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  by_cases hh : c.input.head = 0
  · have hr : c.input.read = .start := by change c.input.cells _ = .start; rw [hh]; exact hi.1
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, markerDir, hr, hh, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp only [hw, ↓reduceIte]
      exact writeAndMove_readBack _ hw .stay
    · exact transitionTape_eq_self hout
  · have hr := hi.read_ne_start (by omega)
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, markerDir, hr, hh, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp only [hw, ↓reduceIte]
      exact writeAndMove_readBack _ hw .stay
    · exact transitionTape_eq_self hout

theorem rewind_input_run (k : ℕ) (c : Cfg 1 machine.Q) (hq : c.state = (1,false))
    (hw : (c.work 0).read ≠ .start) (hout : c.output.read ≠ .start)
    (hi : c.input.StartInvariant) (hh : c.input.head = k) :
    ∃ d, machine.reachesIn (k+1) c d ∧ d.state = (2,false) ∧
      d.input.head = 1 ∧ d.input.cells = c.input.cells ∧ d.work = c.work ∧ d.output = c.output := by
  induction k generalizing c with
  | zero =>
    have hs := rewind_input_step c hq hw hout hi
    simp only [hh, ↓reduceIte] at hs
    refine ⟨_, .step hs .zero, rfl, ?_, rfl, rfl, rfl⟩
    simp [Tape.move, hh]
  | succ k ih =>
    let d : Cfg 1 machine.Q := { c with input := c.input.move .left }
    have hs : machine.step c = some d := by
      simpa only [d, hh, Nat.succ_ne_zero, ↓reduceIte, hq] using rewind_input_step c hq hw hout hi
    have hdhead : d.input.head = k := by simp [d, Tape.move, hh]
    obtain ⟨e, he, hqe, hhead, hcells, hwork, ho⟩ := ih d hq hw hout (hi.move .left) hdhead
    exact ⟨e, .step hs he, hqe, hhead, hcells, hwork, ho⟩

theorem rewind_work_step (c : Cfg 1 machine.Q) (hq : c.state = (2,false))
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hw : (c.work 0).StartInvariant) :
    machine.step c = some { c with
      state := if (c.work 0).head = 0 then (3,false) else (2,false),
      work := fun j => (c.work j).move (if (c.work 0).head = 0 then .right else .left) } := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  by_cases hh : (c.work 0).head = 0
  · have hr : (c.work 0).read = .start := by change (c.work 0).cells _ = .start; rw [hh]; exact hw.1
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, markerDir, hin, hr, hh, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [hr, Tape.writeAndMove, Tape.write, hh]
    · exact transitionTape_eq_self hout
  · have hr := hw.read_ne_start (by omega)
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, markerDir, hin, hr, hh, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp only [hr, ↓reduceIte]
      exact writeAndMove_readBack _ hr .left
    · exact transitionTape_eq_self hout

theorem rewind_work_run (k : ℕ) (c : Cfg 1 machine.Q) (hq : c.state = (2,false))
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hw : (c.work 0).StartInvariant) (hh : (c.work 0).head = k) :
    ∃ d, machine.reachesIn (k+1) c d ∧ machine.halted d ∧
      (d.work 0).head = 1 ∧ (d.work 0).cells = (c.work 0).cells ∧ d.input = c.input ∧ d.output = c.output := by
  induction k generalizing c with
  | zero =>
    have hs := rewind_work_step c hq hin hout hw
    simp only [hh, ↓reduceIte] at hs
    refine ⟨_, .step hs .zero, rfl, ?_, rfl, rfl, rfl⟩
    simp [Tape.move, hh]
  | succ k ih =>
    let d : Cfg 1 machine.Q := { c with work := fun j => (c.work j).move .left }
    have hs : machine.step c = some d := by
      simpa only [d, hh, Nat.succ_ne_zero, ↓reduceIte, hq] using rewind_work_step c hq hin hout hw
    have hdhead : (d.work 0).head = k := by simp [d, Tape.move, hh]
    obtain ⟨e, he, hh, hhead, hcells, hi, ho⟩ := ih d hq hin hout (hw.move .left) hdhead
    exact ⟨e, .step hs he, hh, hhead, hcells, hi, ho⟩

end UnconstrainedPACDetection.VerifierAccumulate

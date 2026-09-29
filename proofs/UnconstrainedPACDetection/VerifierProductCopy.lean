module

public import proofs.UnconstrainedPACDetection.VerifierProductPhases

@[expose] public section

/-! Execute the actual accumulator-to-temporary copy, retaining full tape frames. -/
namespace UnconstrainedPACDetection.VerifierProductMachine
open Complexity
open Complexity.TM

def copyAccumulatorBit (c : Cfg 3 machine.Q) (b : Bool) : Cfg 3 machine.Q :=
  { c with work := ![c.work 0, (c.work 1).move .right,
      (c.work 2).writeAndMove (Γ.ofBool b) .right] }

theorem copy_cons_step (flag b : Bool) (xs emitted : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (2, flag, false))
    (hin : c.input.read ≠ .start) (hm : (c.work 0).read ≠ .start) (hout : c.output.read ≠ .start)
    (hx : (c.work 1).HasBinarySuffix (b :: xs)) (ho : (c.work 2).HasBinaryPrefix emitted) :
    machine.step c = some (copyAccumulatorBit c b) := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  have ht : (c.work 2).read ≠ .start := by rw [ho.read_blank]; decide
  have ha : (c.work 1).read ≠ .start := hx.read_ne_start
  cases b <;> simp only [TM.step, hn, ↓reduceIte]
  all_goals
    have keep := write_readBack (c.work 1) ha
    simp only [hx.read_cons, Γ.ofBool] at keep
    simp only [machine, hq, control, markerDir, hin, hx.read_cons]
    congr 1
    apply Cfg.ext
    · simp [copyAccumulatorBit, Γ.ofBool, hq]
    · rfl
    · funext j
      fin_cases j <;> simp [copyAccumulatorBit, hm, ht, hx.read_cons, Γ.ofBool, Tape.move]
      all_goals
        first
        | exact write_readBack _ hm
        | exact ⟨congrArg Tape.head keep, congrArg Tape.cells keep⟩
        | exact ⟨rfl, rfl⟩
    · exact transitionTape_eq_self hout

theorem copy_nil_step (flag : Bool) (emitted : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (2, flag, false))
    (hin : c.input.read ≠ .start) (hm : (c.work 0).read ≠ .start) (hout : c.output.read ≠ .start)
    (hx : (c.work 1).HasBinarySuffix []) (ho : (c.work 2).HasBinaryPrefix emitted) :
    machine.step c = some { c with
      state := (3, flag, false),
      work := ![c.work 0, (c.work 1).move .left, c.work 2] } := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  have ht : (c.work 2).read ≠ .start := by rw [ho.read_blank]; decide
  have ha : (c.work 1).read ≠ .start := hx.read_ne_start
  simp only [TM.step, hn, ↓reduceIte]
  simp only [machine, hq, control, markerDir, hin, hx.read_nil]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    fin_cases j
    · change (c.work 0).writeAndMove (readBackWrite (c.work 0).read).toΓ
        (if (c.work 0).read = .start then .right else .stay) = c.work 0
      rw [ite_eq_right hm]
      exact writeAndMove_readBack _ hm .stay
    · change (c.work 1).writeAndMove (readBackWrite (c.work 1).read).toΓ
        (if (c.work 1).read = .start then .right else .left) = (c.work 1).move .left
      rw [ite_eq_right ha]
      exact writeAndMove_readBack (c.work 1) ha .left
    · change (c.work 2).writeAndMove (readBackWrite (c.work 2).read).toΓ
        (if (c.work 2).read = .start then .right else .stay) = c.work 2
      rw [ite_eq_right ht]
      exact writeAndMove_readBack _ ht .stay
  · exact transitionTape_eq_self hout

/-- Phase2 copies the whole source suffix, then moves its head left for erasure.
The temporary prefix includes a blank tail, not just a terminating blank cell. -/
theorem copy_run (flag : Bool) (xs emitted : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (2, flag, false))
    (hin : c.input.read ≠ .start) (hm : (c.work 0).read ≠ .start) (hout : c.output.read ≠ .start)
    (hx : (c.work 1).HasBinarySuffix xs) (ho : (c.work 2).HasBinaryPrefix emitted)
    (htail : ∀ j, (c.work 1).head + xs.length ≤ j → (c.work 1).cells j = .blank) :
    ∃ d, machine.reachesIn (xs.length+1) c d ∧ d.state = (3, flag, false) ∧
      (d.work 2).HasBinaryPrefix (emitted ++ xs) ∧
      (d.work 1).head = (c.work 1).head + xs.length - 1 ∧
      (d.work 1).cells = (c.work 1).cells ∧ blankAbove (d.work 1) ∧
      d.input = c.input ∧ d.work 0 = c.work 0 ∧ d.output = c.output := by
  induction xs generalizing emitted c with
  | nil =>
    have hs := copy_nil_step flag emitted c hq hin hm hout hx ho
    refine ⟨_, .step hs .zero, rfl, ?_, ?_, rfl, ?_, rfl, rfl, rfl⟩
    · simpa using ho
    · simp [Tape.move]
    · intro j hj
      change (c.work 1).cells j = .blank
      have hp := hx.1
      change (c.work 1).head - 1 < j at hj
      exact htail j (by simp only [List.length_nil, Nat.add_zero]; omega)
  | cons b xs ih =>
    let s := copyAccumulatorBit c b
    have hs : machine.step c = some s := copy_cons_step flag b xs emitted c hq hin hm hout hx ho
    have hxs : (s.work 1).HasBinarySuffix xs := hx.move_right_cons
    have hos : (s.work 2).HasBinaryPrefix (emitted ++ [b]) := by
      simpa [s, copyAccumulatorBit] using Tape.hasBinaryPrefix_write_bit b ho
    have htails : ∀ j, (s.work 1).head + xs.length ≤ j → (s.work 1).cells j = .blank := by
      intro j hj
      apply htail j
      change (c.work 1).head + 1 + xs.length ≤ j at hj
      simp only [List.length_cons]
      omega
    obtain ⟨d, hd, hqd, hod, hhd, hcd, hbd, hid, hmd, houtd⟩ :=
      ih (emitted ++ [b]) s hq hin hm hout hxs hos htails
    refine ⟨d, .step hs hd, hqd, ?_, ?_, hcd, hbd, hid, hmd, houtd⟩
    · simpa only [List.append_assoc, List.singleton_append] using hod
    · change (d.work 1).head = ((c.work 1).move .right).head + xs.length - 1 at hhd
      simp only [Tape.move, List.length_cons] at *
      omega

end UnconstrainedPACDetection.VerifierProductMachine

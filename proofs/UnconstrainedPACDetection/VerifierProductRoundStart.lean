module

public import proofs.UnconstrainedPACDetection.VerifierProductLoop

@[expose] public section

/-! The actual multiplication round from loop entry to the addition boundary. -/
namespace UnconstrainedPACDetection.VerifierProductMachine
open Complexity
open Complexity.TM

theorem round_prepare_run (b : Bool) (xs : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (1, false, false)) (hm : (c.work 0).read = Γ.ofBool b)
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hx : (c.work 1).HasBinaryString xs) (ha : (c.work 1).StartInvariant)
    (ht : c.work 2 = (Tape.init []).move .right) :
    ∃ d, machine.reachesIn (3 * xs.length + 6) c d ∧
      d.state = (5, b, false) ∧ d.work 1 = (Tape.init []).move .right ∧
      (d.work 2).HasBinaryString (false :: xs) ∧ (d.work 2).cells 0 = .start ∧
      d.input = c.input ∧ d.work 0 = c.work 0 ∧ d.output = c.output := by
  let s : Cfg 3 machine.Q := { c with
    state := (2, b, false),
    work := ![c.work 0, c.work 1, (c.work 2).writeAndMove .zero .right] }
  have haRead : (c.work 1).read ≠ .start := hx.hasBinarySuffix.read_ne_start
  have htRead : (c.work 2).read ≠ .start := by rw [ht]; simp
  have hs : machine.step c = some s := loop_enter_step b c hq hm hin hout haRead htRead
  have hmOff : (c.work 0).read ≠ .start := by rw [hm]; exact Γ.ofBool_ne_start b
  have hp : (s.work 2).HasBinaryPrefix [false] := by
    change ((c.work 2).writeAndMove .zero .right).HasBinaryPrefix [false]
    rw [ht]
    exact Tape.hasBinaryPrefix_write_bit false Tape.init_nil_move_right_hasBinaryPrefix_nil
  have htail : ∀ j, (s.work 1).head + xs.length ≤ j → (s.work 1).cells j = .blank := by
    intro j hj
    change (c.work 1).cells j = .blank
    change (c.work 1).head + xs.length ≤ j at hj
    rw [hx.1] at hj
    have he : j = (j-1)+1 := by omega
    rw [he]
    exact hx.2.2 (j-1) (by omega)
  have ht0 : (s.work 2).cells 0 = .start := by
    change ((c.work 2).writeAndMove .zero .right).cells 0 = .start
    apply Tape.write_move_cell0
    rw [ht]; rfl
  obtain ⟨d, hd, hqd, had, htd, ht0d, hid, hmd, hod⟩ :=
    copy_prepare_run b xs [false] s rfl hin hmOff hout hx.hasBinarySuffix hp htail ha ht0
  refine ⟨d, ?_, hqd, had, ?_, ht0d, hid, hmd, hod⟩
  · convert TM.reachesIn.step hs hd using 1
    change 3 * xs.length + 6 = (c.work 1).head + [false].length + 3 * xs.length + 3 + 1
    rw [hx.1]
    simp
    omega
  · simpa only [List.singleton_append] using htd

end UnconstrainedPACDetection.VerifierProductMachine

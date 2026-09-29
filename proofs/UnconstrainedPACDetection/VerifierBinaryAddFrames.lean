module

public import proofs.UnconstrainedPACDetection.VerifierBinaryAdd

@[expose] public section

/-! Strengthen the actual binary adder execution with the tape positions and
contents required by the multiplier's following rewind phases. -/
namespace UnconstrainedPACDetection.VerifierBinaryAdd
open Complexity
open Complexity.TM

theorem step_frame (carryIn : Bool) (c d : Cfg 1 machine.Q)
    (hq : c.state = some carryIn) (hi : c.input.read ≠ .start)
    (hw : (c.work 0).read ≠ .start) (hs : machine.step c = some d) :
    d.input.head = c.input.head + (if c.input.read = .blank then 0 else 1) ∧
    d.input.cells = c.input.cells ∧
    (d.work 0).head = (c.work 0).head + (if (c.work 0).read = .blank then 0 else 1) ∧
    (d.work 0).cells = (c.work 0).cells := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  have hns : ¬ (c.input.read = .start ∨ (c.work 0).read = .start) := not_or.mpr ⟨hi, hw⟩
  simp only [TM.step, hn, ↓reduceIte] at hs
  simp only [machine, hq, hns, ↓reduceIte] at hs
  split at hs
  · rename_i hb
    cases hs
    dsimp only
    rw [writeAndMove_readBack _ hw]
    simp [idleDir, hb.1, hb.2, Tape.move]
  · cases hs
    dsimp only
    rw [writeAndMove_readBack _ hw]
    by_cases hib : c.input.read = .blank <;>
      by_cases hwb : (c.work 0).read = .blank <;>
      simp [advance, hib, hwb, Tape.move]

theorem suffix_advance_count {t : Tape} {xs : List Bool} (h : t.HasBinarySuffix xs) :
    (if t.read = .blank then 0 else 1) + xs.tail.length = xs.length := by
  cases xs with
  | nil => simp [h.read_nil]
  | cons b xs => cases b <;> simp [h.read_cons, Γ.ofBool, Nat.add_comm]

/-- Complete adder return boundary: arithmetic output, both exhausted
cursors, exact final head positions, and both operand contents unchanged. -/
theorem boundary_full (xs ys : List Bool) (carryIn : Bool) (c : Cfg 1 machine.Q)
    (hq : c.state = some carryIn) (hx : c.input.HasBinarySuffix xs)
    (hy : (c.work 0).HasBinarySuffix ys) (emitted : List Bool)
    (ho : c.output.HasBinaryPrefix emitted) :
    ∃ d, machine.reachesIn (max xs.length ys.length + 1) c d ∧ machine.halted d ∧
      d.output.HasBinaryPrefix (emitted ++ add carryIn xs ys) ∧
      d.input.HasBinarySuffix [] ∧ (d.work 0).HasBinarySuffix [] ∧
      d.input.head = c.input.head + xs.length ∧ d.input.cells = c.input.cells ∧
      (d.work 0).head = (c.work 0).head + ys.length ∧ (d.work 0).cells = (c.work 0).cells := by
  by_cases hempty : xs = [] ∧ ys = []
  · obtain ⟨rfl, rfl⟩ := hempty
    obtain ⟨d, hd, hh, hout⟩ := halt_empty carryIn c hq hx hy emitted ho
    obtain ⟨s, hs, hz⟩ := (machine.reachesIn_succ_iff).mp hd
    have he : s = d := by cases hz; rfl
    subst s
    obtain ⟨hi, hc, hw, hwc⟩ := step_frame carryIn c d hq hx.read_ne_start hy.read_ne_start hs
    have hinput : d.input = c.input := Tape.ext (by simpa [hx.read_nil] using hi) hc
    have hwork : d.work 0 = c.work 0 := Tape.ext (by simpa [hy.read_nil] using hw) hwc
    refine ⟨d, hd, hh, hout, ?_, ?_, ?_, hc, ?_, hwc⟩
    · simpa only [hinput] using hx
    · simpa only [hwork] using hy
    · simpa only [List.length_nil, Nat.add_zero] using congrArg Tape.head hinput
    · simpa only [List.length_nil, Nat.add_zero] using congrArg Tape.head hwork
  · have hne : xs ≠ [] ∨ ys ≠ [] := by tauto
    obtain ⟨s, hs, hq', hx', hy', ho'⟩ := scan_step xs ys carryIn c hq hx hy hne emitted ho
    obtain ⟨hi, hc, hw, hwc⟩ := step_frame carryIn c s hq hx.read_ne_start hy.read_ne_start hs
    obtain ⟨d, hd, hh, hout, hdx, hdy, hdi, hdc, hdw, hdwc⟩ :=
      boundary_full xs.tail ys.tail (carry (xs.headD false) (ys.headD false) carryIn)
        s hq' hx' hy' _ ho'
    have hpositive : 0 < xs.length + ys.length := by
      by_contra h
      apply hempty
      exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
    have hlen : max xs.tail.length ys.tail.length + 1 = max xs.length ys.length := by
      simp only [List.length_tail]
      omega
    have hadd : add carryIn xs ys = digit (xs.headD false) (ys.headD false) carryIn ::
        add (carry (xs.headD false) (ys.headD false) carryIn) xs.tail ys.tail := by
      cases xs <;> cases ys
      · simp at hempty
      all_goals simp only [add, List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil]
    refine ⟨d, ?_, hh, ?_, hdx, hdy, ?_, hdc.trans hc, ?_, hdwc.trans hwc⟩
    · simpa only [hlen] using TM.reachesIn.step hs hd
    · simpa only [hadd, List.append_assoc, List.singleton_append] using hout
    · have hcount := suffix_advance_count hx
      omega
    · have hcount := suffix_advance_count hy
      omega
termination_by xs.length + ys.length
decreasing_by
  all_goals
    have hpositive : 0 < xs.length + ys.length := by
      by_contra h
      apply hempty
      exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
    simp_wf
    omega

end UnconstrainedPACDetection.VerifierBinaryAdd

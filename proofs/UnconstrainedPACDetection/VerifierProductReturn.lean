module

public import proofs.UnconstrainedPACDetection.VerifierProductPhases

@[expose] public section

/-! Compose the fixed multiplier's post-addition cleanup into its loop return. -/
namespace UnconstrainedPACDetection.VerifierProductMachine
open Complexity
open Complexity.TM

/-- Actual phases 6, 7 and 8, including temporary erasure and the single
multiplier decrement. No caller tape contents are changed. -/
theorem cleanup_run (c : Cfg 3 machine.Q) (hq : c.state = (6, false, false))
    (hw : ∀ j, (c.work j).read ≠ .start) (hout : c.output.read ≠ .start)
    (hi : c.input.StartInvariant) (ha : (c.work 1).StartInvariant)
    (ht : (c.work 2).StartInvariant) (hb : blankAbove (c.work 2)) :
    ∃ d, machine.reachesIn (c.input.head + (c.work 2).head + (c.work 1).head + 3) c d ∧
      d.state = (1, false, false) ∧ d.input.head = 1 ∧ d.input.cells = c.input.cells ∧
      (d.work 1).head = 1 ∧ (d.work 1).cells = (c.work 1).cells ∧
      d.work 0 = (c.work 0).move .left ∧ d.work 2 = (Tape.init []).move .right ∧
      d.output = c.output := by
  obtain ⟨a, hca, hqa, hia, hica, hwa, hoa⟩ :=
    rewind_input_run c.input.head c hq hw hout hi rfl
  have hiaStart : a.input.StartInvariant := by
    exact ⟨hica ▸ hi.1, fun j hj => hica ▸ hi.2 j hj⟩
  have hiaRead : a.input.read ≠ .start := hiaStart.read_ne_start (by omega)
  have hwaRead : ∀ j, j ≠ eraseIndex true → (a.work j).read ≠ .start := by
    intro j _; simpa only [hwa] using hw j
  obtain ⟨b, hab, hqb, htb, hib, hob, hwb⟩ :=
    erase_run true false (c.work 2).head a hqa hiaRead
      (by simpa only [hoa] using hout) hwaRead
      (by simpa only [hwa, eraseIndex, ↓reduceIte] using ht) (by simp only [hwa]; rfl)
      (by simpa only [hwa, eraseIndex, ↓reduceIte] using hb)
  have hb0 : b.work 0 = c.work 0 := (hwb 0 (by decide)).trans (congrFun hwa 0)
  have hb1 : b.work 1 = c.work 1 := (hwb 1 (by decide)).trans (congrFun hwa 1)
  obtain ⟨d, hbd, hqd, had, hacd, hmd, htd, hid, hod⟩ :=
    rewind_acc_run (c.work 1).head b hqb
      (by simpa only [hib] using hiaRead) (by simpa only [hob, hoa] using hout)
      (by simpa only [hb0] using hw 0) (by change (b.work (eraseIndex true)).read ≠ .start; rw [htb]; simp)
      (by simpa only [hb1] using ha) (by rw [hb1])
  refine ⟨d, ?_, hqd, ?_, ?_, had, ?_, ?_, htd.trans htb, hod.trans (hob.trans hoa)⟩
  · convert machine.reachesIn_trans (machine.reachesIn_trans hca hab) hbd using 1
    omega
  · simpa only [hid, hib] using hia
  · simpa only [hid, hib] using hica
  · simpa only [hb1] using hacd
  · simpa only [hb0] using hmd

end UnconstrainedPACDetection.VerifierProductMachine

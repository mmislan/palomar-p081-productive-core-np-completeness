module

public import proofs.UnconstrainedPACDetection.VerifierProductCopy
public import proofs.Complexitylib.Models.TuringMachine.Internal

@[expose] public section

/-! Consume the actual copy boundary in accumulator erasure and temporary rewind. -/
namespace UnconstrainedPACDetection.VerifierProductMachine
open Complexity
open Complexity.TM

/-- Concrete phase2-to5 preparation. The blank-tail assumption rules out
unseen source data beyond the suffix terminator. -/
theorem copy_prepare_run (flag : Bool) (xs emitted : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (2, flag, false))
    (hin : c.input.read ≠ .start) (hm : (c.work 0).read ≠ .start) (hout : c.output.read ≠ .start)
    (hx : (c.work 1).HasBinarySuffix xs) (ho : (c.work 2).HasBinaryPrefix emitted)
    (htail : ∀ j, (c.work 1).head + xs.length ≤ j → (c.work 1).cells j = .blank)
    (ha : (c.work 1).StartInvariant) (ht0 : (c.work 2).cells 0 = .start) :
    ∃ d, machine.reachesIn ((c.work 1).head + emitted.length + 3 * xs.length + 3) c d ∧
      d.state = (5, flag, false) ∧ d.work 1 = (Tape.init []).move .right ∧
      (d.work 2).HasBinaryString (emitted ++ xs) ∧ (d.work 2).cells 0 = .start ∧
      d.input = c.input ∧ d.work 0 = c.work 0 ∧ d.output = c.output := by
  obtain ⟨a, hca, hqa, hpa, hha, hcells, hblank, hia, hma, hoa⟩ :=
    copy_run flag xs emitted c hq hin hm hout hx ho htail
  have haStart : (a.work 1).StartInvariant := by
    exact ⟨hcells ▸ ha.1, fun j hj => hcells ▸ ha.2 j hj⟩
  have htStart : (a.work 2).StartInvariant :=
    ⟨work_cells_zero_eq_start_of_reachesIn 2 hca ht0,
      Tape.cells_ne_start_of_hasBinaryPrefix hpa⟩
  have htRead : (a.work 2).read ≠ .start := by rw [hpa.read_blank]; decide
  obtain ⟨d, had, hqd, hacc, hth, htc, hid, hod, hmd⟩ :=
    prepare_add_run flag a hqa (by simpa only [hia] using hin)
      (by simpa only [hoa] using hout) (by simpa only [hma] using hm)
      htRead haStart hblank htStart
  refine ⟨d, ?_, hqd, hacc, Tape.hasBinaryString_of_hasBinaryPrefix hpa hth htc,
    ?_, hid.trans hia, hmd.trans hma, hod.trans hoa⟩
  · convert machine.reachesIn_trans hca had using 1
    have hh := hpa.1
    have hp := hx.1
    simp only [List.length_append] at hh
    omega
  · rw [htc]
    exact htStart.1

end UnconstrainedPACDetection.VerifierProductMachine

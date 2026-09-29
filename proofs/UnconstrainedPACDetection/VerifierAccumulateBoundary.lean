module

public import proofs.UnconstrainedPACDetection.VerifierAccumulateReturn
public import proofs.Complexitylib.Models.TuringMachine.Internal

@[expose] public section

/-! Reusable actual in-place addition, with exact complete execution time. -/
namespace UnconstrainedPACDetection.VerifierAccumulate
open Complexity
open Complexity.TM

theorem accumulation_run (xs ys : List Bool) (c : Cfg 1 machine.Q)
    (hq : c.state = machine.qstart)
    (hx : c.input.HasBinaryString xs) (hi : c.input.StartInvariant)
    (hy : (c.work 0).HasBinaryString ys) (hz : (c.work 0).cells 0 = .start)
    (hout : c.output.read ≠ .start) :
    ∃ d, machine.reachesIn
        (max xs.length ys.length + xs.length + (VerifierBinaryAdd.add false xs ys).length + 5) c d ∧
      machine.halted d ∧ (d.work 0).HasBinaryString (VerifierBinaryAdd.add false xs ys) ∧
      (d.work 0).cells 0 = .start ∧ d.input = c.input ∧ d.output = c.output := by
  have hsplit : Split (c.work 0) [] ys := by
    simpa only [Split, List.length_nil, List.nil_append, Tape.HasBinaryString,
      Tape.HasBinaryContent] using hy
  obtain ⟨a, hca, hqa, hsa, _, hhia, hcia, hoa⟩ :=
    scan_boundary xs ys [] false c hq hx.hasBinarySuffix hsplit hout
  have hpa : (a.work 0).HasBinaryPrefix (VerifierBinaryAdd.add false xs ys) := by
    simpa only [Split, List.nil_append, List.append_nil, Tape.HasBinaryContent, Tape.HasBinaryPrefix] using hsa
  have hza : (a.work 0).cells 0 = .start := work_cells_zero_eq_start_of_reachesIn 0 hca hz
  have hwa : (a.work 0).StartInvariant := ⟨hza, Tape.cells_ne_start_of_hasBinaryPrefix hpa⟩
  have hia : a.input.StartInvariant := ⟨hcia ▸ hi.1, fun j hj => hcia ▸ hi.2 j hj⟩
  obtain ⟨b, hab, hqb, hhib, hcib, hwb, hob⟩ :=
    rewind_input_run a.input.head a hqa (by rw [hpa.read_blank]; decide)
      (by simpa only [hoa] using hout) hia rfl
  have hib : b.input.StartInvariant := ⟨hcib ▸ hia.1, fun j hj => hcib ▸ hia.2 j hj⟩
  obtain ⟨d, hbd, hhalt, hhd, hcd, hid, hod⟩ :=
    rewind_work_run (a.work 0).head b hqb (hib.read_ne_start (by omega))
      (by simpa only [hob, hoa] using hout)
      (by simpa only [hwb] using hwa) (by rw [hwb])
  have hcd' : (d.work 0).cells = (a.work 0).cells := by simpa only [hwb] using hcd
  refine ⟨d, ?_, hhalt, Tape.hasBinaryString_of_hasBinaryPrefix hpa hhd hcd',
    hcd' ▸ hza, ?_, hod.trans (hob.trans hoa)⟩
  · convert machine.reachesIn_trans (machine.reachesIn_trans hca hab) hbd using 1
    have hphead := hpa.1
    have hxhead := hx.1
    omega
  · apply Tape.ext
    · simpa only [hid] using hhib.trans hx.1.symm
    · exact (congrArg Tape.cells hid).trans (hcib.trans hcia)

/-- The same reusable operation has a linear bound in operand bit lengths.
No buffer copying, reinitialization or head movement is omitted. -/
theorem accumulation_bounded_run (xs ys : List Bool) (c : Cfg 1 machine.Q)
    (hq : c.state = machine.qstart)
    (hx : c.input.HasBinaryString xs) (hi : c.input.StartInvariant)
    (hy : (c.work 0).HasBinaryString ys) (hz : (c.work 0).cells 0 = .start)
    (hout : c.output.read ≠ .start) :
    ∃ t d bits, t ≤ xs.length + 2 * max xs.length ys.length + 6 ∧
      machine.reachesIn t c d ∧ machine.halted d ∧ (d.work 0).HasBinaryString bits ∧
      BinaryFields.readNat bits = BinaryFields.readNat xs + BinaryFields.readNat ys ∧
      (d.work 0).cells 0 = .start ∧ d.input = c.input ∧ d.output = c.output := by
  obtain ⟨d, hd, hh, hp, hz', hi', ho⟩ := accumulation_run xs ys c hq hx hi hy hz hout
  refine ⟨_, d, VerifierBinaryAdd.add false xs ys, ?_, hd, hh, hp, ?_, hz', hi', ho⟩
  · have h := VerifierBinaryAdd.add_length false xs ys
    omega
  · simpa using VerifierBinaryAdd.add_value false xs ys

end UnconstrainedPACDetection.VerifierAccumulate

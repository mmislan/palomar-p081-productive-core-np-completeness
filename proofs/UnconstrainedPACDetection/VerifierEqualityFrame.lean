module

public import proofs.UnconstrainedPACDetection.VerifierBinaryEquality

@[expose] public section

namespace UnconstrainedPACDetection.VerifierBinaryEquality
open Complexity Complexity.TM
open VerifierBinaryAdd (bit advance advance_right suffix_bit suffix_advance)

theorem scan_frame (xs ys : List Bool) (prior : Bool) (s : Cfg 1 machine.Q)
    (hs : s.state = some prior) (hx : s.input.HasBinarySuffix xs)
    (hy : (s.work 0).HasBinarySuffix ys) (hne : xs ≠ [] ∨ ys ≠ [])
    (emitted : List Bool) (ho : s.output.HasBinaryPrefix emitted) :
    ∃ d, machine.step s = some d ∧
      d.state = some (next (xs.headD false) (ys.headD false) prior) ∧
      d.input.HasBinarySuffix xs.tail ∧ (d.work 0).HasBinarySuffix ys.tail ∧
      d.output.HasBinaryPrefix emitted ∧ d.input.cells = s.input.cells ∧
      (d.work 0).cells = (s.work 0).cells := by
  have hnstart : ¬(s.input.read = .start ∨ (s.work 0).read = .start) :=
    not_or.mpr ⟨hx.read_ne_start, hy.read_ne_start⟩
  have hnblank : ¬(s.input.read = .blank ∧ (s.work 0).read = .blank) := by
    rcases hne with h | h
    · cases xs with
      | nil => contradiction
      | cons a xs => cases a <;> simp [hx.read_cons, Γ.ofBool]
    · cases ys with
      | nil => contradiction
      | cons b ys => cases b <;> simp [hy.read_cons, Γ.ofBool]
  let d : Cfg 1 machine.Q :=
    { state := some (next (bit s.input.read) (bit (s.work 0).read) prior)
      input := s.input.move (advance s.input.read)
      work := fun j => (s.work j).writeAndMove (readBackWrite (s.work j).read)
        (advance (s.work j).read)
      output := s.output.writeAndMove (readBackWrite s.output.read) (idleDir s.output.read) }
  refine ⟨d, ?_, ?_, suffix_advance hx, ?_, ?_, ?_, ?_⟩
  · simp [TM.step, machine, hs, hnstart, hnblank, d]
  · simp only [d, suffix_bit hx, suffix_bit hy]
    rfl
  · change ((s.work 0).writeAndMove _ _).HasBinarySuffix ys.tail
    rw [writeAndMove_readBack _ hy.read_ne_start]
    exact suffix_advance hy
  · have keep : s.output.writeAndMove (readBackWrite s.output.read).toΓ
        (idleDir s.output.read) = s.output :=
      transitionTape_eq_self (by rw [ho.read_blank]; decide)
    simpa only [d, keep] using ho
  · exact Tape.move_cells _ _
  · change ((s.work 0).writeAndMove _ _).cells = _
    rw [writeAndMove_readBack _ hy.read_ne_start]
    exact Tape.move_cells _ _

theorem halt_frame (prior : Bool) (s : Cfg 1 machine.Q)
    (hs : s.state = some prior) (hx : s.input.HasBinarySuffix [])
    (hy : (s.work 0).HasBinarySuffix [])
    (emitted : List Bool) (ho : s.output.HasBinaryPrefix emitted) :
    ∃ d, machine.reachesIn 1 s d ∧ machine.halted d ∧
      d.output.HasBinaryPrefix (emitted ++ [prior]) ∧
      d.input.HasBinarySuffix [] ∧ (d.work 0).HasBinarySuffix [] ∧
      d.input.cells = s.input.cells ∧ (d.work 0).cells = (s.work 0).cells := by
  let d : Cfg 1 machine.Q :=
    { state := none
      input := s.input.move (idleDir s.input.read)
      work := fun j => (s.work j).writeAndMove (readBackWrite (s.work j).read)
        (idleDir (s.work j).read)
      output := s.output.writeAndMove (Γ.ofBool prior) .right }
  have step : machine.step s = some d := by
    cases prior <;> simp [TM.step, machine, hs, hx.read_nil, hy.read_nil, d, Γ.ofBool, readBackWrite]
  have hi : d.input = s.input := by simp [d, hx.read_nil, idleDir, Tape.move]
  have hw : d.work 0 = s.work 0 := by
    change (s.work 0).writeAndMove _ _ = _
    rw [writeAndMove_readBack _ hy.read_ne_start]
    simp [hy.read_nil, idleDir, Tape.move]
  exact ⟨d, .step step .zero, rfl, Tape.hasBinaryPrefix_write_bit prior ho,
    hi ▸ hx, hw ▸ hy, congrArg Tape.cells hi, congrArg Tape.cells hw⟩

theorem boundary_frame (xs ys : List Bool) (prior : Bool) (s : Cfg 1 machine.Q)
    (hs : s.state = some prior) (hx : s.input.HasBinarySuffix xs)
    (hy : (s.work 0).HasBinarySuffix ys)
    (emitted : List Bool) (ho : s.output.HasBinaryPrefix emitted) :
    ∃ d, machine.reachesIn (max xs.length ys.length + 1) s d ∧ machine.halted d ∧
      d.output.HasBinaryPrefix (emitted ++ [compare prior xs ys]) ∧
      d.input.HasBinarySuffix [] ∧ (d.work 0).HasBinarySuffix [] ∧
      d.input.cells = s.input.cells ∧ (d.work 0).cells = (s.work 0).cells := by
  by_cases hempty : xs = [] ∧ ys = []
  · obtain ⟨rfl, rfl⟩ := hempty
    simpa only [List.length_nil, max_self, Nat.zero_add, compare] using
      halt_frame prior s hs hx hy emitted ho
  · have hne : xs ≠ [] ∨ ys ≠ [] := by tauto
    obtain ⟨s', hstep, hstate, hx', hy', ho', hic, hwc⟩ := scan_frame xs ys prior s hs hx hy hne emitted ho
    obtain ⟨d, hd, hh, hout, hxe, hye, hix, hwx⟩ := boundary_frame xs.tail ys.tail
      (next (xs.headD false) (ys.headD false) prior) s' hstate hx' hy' emitted ho'
    have hpositive : 0 < xs.length + ys.length := by
      by_contra h
      apply hempty
      exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
    have hlen : max xs.tail.length ys.tail.length + 1 = max xs.length ys.length := by
      simp only [List.length_tail]
      omega
    have hcompare : compare prior xs ys =
        compare (next (xs.headD false) (ys.headD false) prior) xs.tail ys.tail := by
      cases xs <;> cases ys
      · simp at hempty
      all_goals simp only [compare, List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil]
    refine ⟨d, ?_, hh, ?_, hxe, hye, hix.trans hic, hwx.trans hwc⟩
    · simpa only [hlen] using TM.reachesIn.step hstep hd
    · simpa only [hcompare] using hout
termination_by xs.length + ys.length
decreasing_by
  all_goals
    have hpositive : 0 < xs.length + ys.length := by
      by_contra h
      apply hempty
      exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
    simp_wf
    omega


end UnconstrainedPACDetection.VerifierBinaryEquality

module

public import proofs.UnconstrainedPACDetection.VerifierProductIteration
public import proofs.UnconstrainedPACDetection.VerifierProductSeek

@[expose] public section

/-! Universal binary multiplication by the fixed three-work-tape machine. -/
namespace UnconstrainedPACDetection.VerifierProductMachine
open Complexity
open Complexity.TM

theorem multiplication_run (xs ys : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (0, false, false))
    (hx : c.input.HasBinaryString xs) (hi : c.input.StartInvariant)
    (hy : (c.work 0).HasBinaryString ys) (hm : (c.work 0).StartInvariant)
    (ha : c.work 1 = (Tape.init []).move .right)
    (ht : c.work 2 = (Tape.init []).move .right) (hout : c.output.read ≠ .start) :
    ∃ t d, t ≤ ys.length + 2 + ys.length * (10*xs.length + 20*ys.length + 30) ∧
      machine.reachesIn t c d ∧ machine.halted d ∧
      (d.work 1).HasBinaryString (VerifierBinaryProduct.multiply xs ys) ∧
      (d.work 1).StartInvariant ∧ d.input = c.input ∧ d.work 0 = c.work 0 ∧
      d.work 2 = (Tape.init []).move .right ∧ d.output = c.output := by
  have hw : ∀ j, j ≠ 0 → (c.work j).read ≠ .start := by
    intro j hj; fin_cases j
    · exact False.elim (hj rfl)
    · change (c.work 1).read ≠ .start
      rw [ha]; simp
    · change (c.work 2).read ≠ .start
      rw [ht]; simp
  obtain ⟨a, hca, hqa, hhead, hcells, hia, hoa, hwa⟩ :=
    seek_run ys c hq hx.hasBinarySuffix.read_ne_start hout hw hy.hasBinarySuffix
  have ha1 : a.work 1 = (Tape.init []).move .right := (hwa 1 (by decide)).trans ha
  have ha2 : a.work 2 = (Tape.init []).move .right := (hwa 2 (by decide)).trans ht
  have hhead' : (a.work 0).head = ys.length := by simpa only [hy.1, Nat.add_sub_cancel_left] using hhead
  have hbits : ∀ i, (h : i < ys.length) → (a.work 0).cells (i+1) = Γ.ofBool (ys[i]'h) := by
    intro i h; rw [hcells]; exact hy.2.1 i h
  have hstart : (a.work 0).StartInvariant :=
    ⟨hcells ▸ hm.1, fun j hj => hcells ▸ hm.2 j hj⟩
  obtain ⟨t, d, hbound, had, hhalt, hres, hds, hid, hdh, hdc, htd, hod⟩ :=
    iterate_run ys xs [] xs.length a hqa hhead' hbits hstart
      (by simpa only [hia] using hx) (by simpa only [hia] using hi)
      (by simpa only [hoa] using hout)
      (by rw [ha1]; exact Tape.init_move_right_hasBinaryString [])
      (by rw [ha1]; exact Tape.StartInvariant.init_nil.move .right) ha2 (by rfl) (by simp)
  refine ⟨ys.length+1+t, d, by omega, machine.reachesIn_trans hca had, hhalt,
    ?_, hds, hid.trans hia, ?_, htd, hod.trans hoa⟩
  · simpa only [← VerifierBinaryProduct.multiply_foldr] using hres
  · exact Tape.ext (hdh.trans hy.1.symm) (hdc.trans hcells)

/-- The returned binary word has the literal product value, with the same
whole-machine polynomial bound and unchanged caller tapes. -/
theorem multiplication_value_run (xs ys : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (0, false, false))
    (hx : c.input.HasBinaryString xs) (hi : c.input.StartInvariant)
    (hy : (c.work 0).HasBinaryString ys) (hm : (c.work 0).StartInvariant)
    (ha : c.work 1 = (Tape.init []).move .right)
    (ht : c.work 2 = (Tape.init []).move .right) (hout : c.output.read ≠ .start) :
    ∃ t d bits, t ≤ ys.length + 2 + ys.length * (10*xs.length + 20*ys.length + 30) ∧
      machine.reachesIn t c d ∧ machine.halted d ∧ (d.work 1).HasBinaryString bits ∧
      BinaryFields.readNat bits = BinaryFields.readNat xs * BinaryFields.readNat ys ∧
      d.input = c.input ∧ d.work 0 = c.work 0 ∧
      d.work 2 = (Tape.init []).move .right ∧ d.output = c.output := by
  obtain ⟨t, d, hb, hr, hh, hp, _, hin, hmult, htemp, ho⟩ :=
    multiplication_run xs ys c hq hx hi hy hm ha ht hout
  exact ⟨t, d, _, hb, hr, hh, hp, VerifierBinaryProduct.multiply_value xs ys, hin, hmult, htemp, ho⟩

end UnconstrainedPACDetection.VerifierProductMachine

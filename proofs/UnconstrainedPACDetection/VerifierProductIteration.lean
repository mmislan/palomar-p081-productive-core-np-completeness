module

public import proofs.UnconstrainedPACDetection.VerifierProductRound

@[expose] public section

/-! Iterate actual rounds right-to-left with a bound on all machine transitions. -/
namespace UnconstrainedPACDetection.VerifierProductMachine
open Complexity
open Complexity.TM

theorem iterate_run (ys xs acc : List Bool) (M : ℕ) (c : Cfg 3 machine.Q)
    (hq : c.state = (1, false, false))
    (hmHead : (c.work 0).head = ys.length)
    (hmBits : ∀ i, (h : i < ys.length) → (c.work 0).cells (i+1) = Γ.ofBool (ys[i]'h))
    (hmStart : (c.work 0).StartInvariant)
    (hx : c.input.HasBinaryString xs) (hi : c.input.StartInvariant)
    (hout : c.output.read ≠ .start)
    (ha : (c.work 1).HasBinaryString acc) (haStart : (c.work 1).StartInvariant)
    (ht : c.work 2 = (Tape.init []).move .right)
    (hxs : xs.length ≤ M) (hacc : acc.length ≤ M) :
    ∃ t d, t ≤ ys.length * (10*M + 20*ys.length + 30) + 1 ∧
      machine.reachesIn t c d ∧ machine.halted d ∧
      (d.work 1).HasBinaryString (ys.foldr (VerifierBinaryProduct.step xs) acc) ∧
      (d.work 1).StartInvariant ∧ d.input = c.input ∧
      (d.work 0).head = 1 ∧ (d.work 0).cells = (c.work 0).cells ∧
      d.work 2 = (Tape.init []).move .right ∧ d.output = c.output := by
  induction ys using List.reverseRecOn generalizing acc M c with
  | nil =>
    have hs := loop_halt_step c hq hmHead hmStart hx.hasBinarySuffix.read_ne_start hout
      ha.hasBinarySuffix.read_ne_start (by rw [ht]; simp)
    refine ⟨1, _, by simp, .step hs .zero, rfl, ?_, ?_, rfl, ?_, rfl, ?_, rfl⟩
    · simpa [replaceWork] using ha
    · simpa [replaceWork] using haStart
    · simp [replaceWork, Tape.move, hmHead]
    · simpa [replaceWork] using ht
  | append_singleton ys b ih =>
    have hm : (c.work 0).read = Γ.ofBool b := by
      change (c.work 0).cells (c.work 0).head = Γ.ofBool b
      rw [hmHead]
      simpa using hmBits ys.length (by simp)
    obtain ⟨a, hca, hqa, haa, has, hia, hma, hta, hoa⟩ :=
      round_run b xs acc c hq hm hx hi hout ha haStart ht
    have hhead : (a.work 0).head = ys.length := by
      rw [hma]
      simp [Tape.move, hmHead]
    have hbits : ∀ i, (h : i < ys.length) → (a.work 0).cells (i+1) = Γ.ofBool (ys[i]'h) := by
      intro i h
      rw [hma]
      exact (hmBits i (by simp only [List.length_append, List.length_singleton]; omega)).trans
        (congrArg Γ.ofBool (List.getElem_append_left h))
    have hstart : (a.work 0).StartInvariant := by rw [hma]; exact hmStart.move .left
    have hlen : (VerifierBinaryProduct.step xs b acc).length ≤ M+2 :=
      (VerifierBinaryProduct.step_length xs acc b).trans (by omega)
    obtain ⟨t, d, hbound, had, hhalt, hres, hdStart, hid, hmh, hmc, htd, hod⟩ :=
      ih (VerifierBinaryProduct.step xs b acc) (M+2) a hqa hhead hbits hstart
        (by simpa only [hia] using hx) (by simpa only [hia] using hi)
        (by simpa only [hoa] using hout) haa has hta (by omega) hlen
    let r := 4 * acc.length + max (if b then xs.length else 0) (acc.length+1) +
      (if b then xs.length else 0) + (VerifierBinaryProduct.step xs b acc).length + 14
    have he : (if b then xs.length else 0) ≤ M := by split <;> omega
    have hmax : max (if b then xs.length else 0) (acc.length+1) ≤ M+1 := by omega
    have hr : r ≤ 10*M + 20*(ys.length+1) + 30 := by dsimp [r]; omega
    refine ⟨r+t, d, ?_, machine.reachesIn_trans hca had, hhalt, ?_, hdStart,
      hid.trans hia, hmh, ?_, htd, hod.trans hoa⟩
    · simp only [List.length_append, List.length_singleton]
      nlinarith
    · simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using hres
    · simpa only [hma, Tape.move_cells] using hmc

end UnconstrainedPACDetection.VerifierProductMachine

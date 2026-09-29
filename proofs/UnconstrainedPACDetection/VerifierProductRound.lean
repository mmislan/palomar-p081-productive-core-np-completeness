module

public import proofs.UnconstrainedPACDetection.VerifierProductRoundStart
public import proofs.UnconstrainedPACDetection.VerifierProductAdd
public import proofs.UnconstrainedPACDetection.VerifierProductReturn

@[expose] public section

/-! One complete round of the fixed multiplier, with arithmetic and exact time. -/
namespace UnconstrainedPACDetection.VerifierProductMachine
open Complexity
open Complexity.TM

theorem round_run (b : Bool) (xs acc : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (1, false, false)) (hm : (c.work 0).read = Γ.ofBool b)
    (hx : c.input.HasBinaryString xs) (hi : c.input.StartInvariant)
    (hout : c.output.read ≠ .start)
    (ha : (c.work 1).HasBinaryString acc) (haStart : (c.work 1).StartInvariant)
    (ht : c.work 2 = (Tape.init []).move .right) :
    ∃ d, machine.reachesIn
        (4 * acc.length + max (if b then xs.length else 0) (acc.length+1) +
          (if b then xs.length else 0) + (VerifierBinaryProduct.step xs b acc).length + 14) c d ∧
      d.state = (1, false, false) ∧
      (d.work 1).HasBinaryString (VerifierBinaryProduct.step xs b acc) ∧
      (d.work 1).StartInvariant ∧ d.input = c.input ∧
      d.work 0 = (c.work 0).move .left ∧ d.work 2 = (Tape.init []).move .right ∧
      d.output = c.output := by
  have hmOff : (c.work 0).read ≠ .start := by rw [hm]; exact Γ.ofBool_ne_start b
  obtain ⟨a, hca, hqa, haa, hta, ht0a, hia, hma, hoa⟩ :=
    round_prepare_run b acc c hq hm hx.hasBinarySuffix.read_ne_start hout ha haStart ht
  have hxa : a.input.HasBinarySuffix xs := by simpa only [hia] using hx.hasBinarySuffix
  have hpa : (a.work 1).HasBinaryPrefix [] := by
    rw [haa]; exact Tape.init_nil_move_right_hasBinaryPrefix_nil
  obtain ⟨z, haz, hqz, hpz, _, htz, hihz, hicz, hthz, htcz, hmz, hoz⟩ :=
    addition_run b xs (false :: acc) [] a hqa hxa hta.hasBinarySuffix hpa
      (by simpa only [hma] using hmOff) (by simpa only [hoa] using hout)
  have heq : VerifierBinaryAdd.add false (if b then xs else []) (false :: acc) =
      VerifierBinaryProduct.step xs b acc := by
    cases b <;> simp [VerifierBinaryProduct.step, add_empty_left]
  have hpz' : (z.work 1).HasBinaryPrefix (VerifierBinaryProduct.step xs b acc) := by
    simpa only [List.nil_append, heq] using hpz
  have hz0 : (z.work 1).cells 0 = .start :=
    work_cells_zero_eq_start_of_reachesIn 1 (machine.reachesIn_trans hca haz) haStart.1
  have hzs : (z.work 1).StartInvariant :=
    ⟨hz0, Tape.cells_ne_start_of_hasBinaryPrefix hpz'⟩
  have hzi : z.input.StartInvariant := by
    have hc : z.input.cells = c.input.cells := hicz.trans (congrArg Tape.cells hia)
    exact ⟨hc ▸ hi.1, fun j hj => hc ▸ hi.2 j hj⟩
  have hzt : (z.work 2).StartInvariant := by
    exact ⟨htcz ▸ ht0a, fun j hj => htcz ▸ Tape.cells_ne_start_of_hasBinaryString hta j hj⟩
  have hblank : blankAbove (z.work 2) := by
    intro j hj
    rw [htcz]
    have hh := hta.1
    simp only [List.length_cons] at hthz
    have he : j = (j-1)+1 := by omega
    rw [he]
    exact hta.2.2 (j-1) (by simp only [List.length_cons]; omega)
  have hwz : ∀ j, (z.work j).read ≠ .start := by
    intro j; fin_cases j
    · change (z.work 0).read ≠ .start
      rw [hmz, hma]; exact hmOff
    · change (z.work 1).read ≠ .start
      rw [hpz'.read_blank]; decide
    · exact htz.read_ne_start
  obtain ⟨d, hzd, hqd, hihd, hicd, hahd, hacd, hmd, htd, hod⟩ :=
    cleanup_run z hqz hwz (by simpa only [hoz, hoa] using hout) hzi hzs hzt hblank
  refine ⟨d, ?_, hqd, Tape.hasBinaryString_of_hasBinaryPrefix hpz' hahd hacd,
    ?_, ?_, ?_, htd, hod.trans (hoz.trans hoa)⟩
  · convert machine.reachesIn_trans (machine.reachesIn_trans hca haz) hzd using 1
    have hhacc := hpz'.1
    have hhtemp := hta.1
    have hhinput := hx.1
    have hhain : a.input.head = 1 := by simpa only [hia] using hhinput
    simp only [List.length_cons] at hthz ⊢
    omega
  · exact ⟨hacd ▸ hzs.1, fun j hj => hacd ▸ hzs.2 j hj⟩
  · apply Tape.ext
    · exact hihd.trans hx.1.symm
    · exact hicd.trans (hicz.trans (congrArg Tape.cells hia))
  · simpa only [hmz, hma] using hmd

end UnconstrainedPACDetection.VerifierProductMachine

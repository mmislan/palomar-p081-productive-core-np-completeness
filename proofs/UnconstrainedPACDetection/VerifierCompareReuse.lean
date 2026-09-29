module

public import proofs.UnconstrainedPACDetection.VerifierTapeCleanup

@[expose] public section

namespace UnconstrainedPACDetection.VerifierCompareReuse
open Complexity Complexity.TM
open VerifierTapeCleanup (safe frame cleared)
open VerifierBufferedProduct (wordTape)

def machine : TM 11 := seqTM VerifierTotalsCompare.machine VerifierTapeCleanup.totals

theorem reuse_hoare (xs ys : List Bool) (w : Fin 11 → Tape) (inp₀ out₀ : Tape)
    (hx : w 7 = wordTape xs) (hy : w 8 = wordTape ys) (hw : safe w)
    (hi : inp₀.read ≠ .start) (ho : out₀.HasBinaryPrefix []) :
    machine.HoareTime (frame w inp₀ out₀)
      (fun inp work out => inp = inp₀ ∧ work = cleared (cleared w 7) 8 ∧
        out.HasBinaryPrefix [VerifierBinaryCompare.compare false xs ys])
      (3*max xs.length ys.length+2*xs.length+2*ys.length+25) := by
  rintro inp work out ⟨hin₀,hwork₀,hout₀⟩
  subst inp
  subst work
  subst out
  let c : Cfg 11 VerifierTotalsCompare.machine.Q :=
    ⟨VerifierTotalsCompare.machine.qstart,inp₀,w,out₀⟩
  have hxs : (c.work 7).HasBinarySuffix xs := by
    change (w 7).HasBinarySuffix xs
    rw [hx]; exact (Tape.init_move_right_hasBinaryString xs).hasBinarySuffix
  have hys : (c.work 8).HasBinarySuffix ys := by
    change (w 8).HasBinarySuffix ys
    rw [hy]; exact (Tape.init_move_right_hasBinaryString ys).hasBinarySuffix
  have hm : (c.work 7).StartInvariant := by
    change (w 7).StartInvariant
    rw [hx]; exact (Tape.StartInvariant.init_ofBool xs).move .right
  obtain ⟨d,hd,hh,hout,hin,hframe,hxe,hye,hxc,hyc⟩ :=
    VerifierTotalsCompare.comparison_frame xs ys c rfl hxs hm hys
      (fun j _ _ => (hw j).1) hi ho
  have hs : safe d.work := by
    intro j
    by_cases h7 : j = 7
    · subst j; exact ⟨hxe.read_ne_start,hxe.1⟩
    by_cases h8 : j = 8
    · subst j; exact ⟨hye.read_ne_start,hye.1⟩
    rw [hframe j h7 h8]; exact hw j
  have hid : d.input.read ≠ .start := by rw [hin]; exact hi
  have hod : d.output.read ≠ .start := by rw [hout.read_blank]; decide
  have hohd : 1 ≤ d.output.head := by rw [hout.1]; simp
  have h7 := VerifierTotalsCompare.machine.work_head_reachesIn_bound hd 7
  have h8 := VerifierTotalsCompare.machine.work_head_reachesIn_bound hd 8
  change (d.work 7).head ≤ (w 7).head+_ at h7
  change (d.work 8).head ≤ (w 8).head+_ at h8
  rw [hx] at h7
  rw [hy] at h8
  have hc := VerifierTapeCleanup.totals_hoare xs ys d.work d.input d.output
    (hxc.trans (congrArg Tape.cells hx)) (hyc.trans (congrArg Tape.cells hy)) hs hid hod hohd
  obtain ⟨e,t,ht,he,heh,hei,hew,heo⟩ := hc d.input d.work d.output ⟨rfl,rfl,rfl⟩
  have htrans := phaseTransition_eq_self_of_reads_ne_start hid (fun j => (hs j).1) hod
  have he' : VerifierTapeCleanup.totals.reachesIn t
      ⟨VerifierTapeCleanup.totals.qstart,transitionInput d.input,
        (fun j => transitionTape (d.work j)),transitionTape d.output⟩ e := by
    simpa only [htrans.1,htrans.2.1,htrans.2.2] using he
  have hr := seqTM_reachesIn_of_reachesIn _ _ hd hh he'
  refine ⟨phase2Wrap VerifierTotalsCompare.machine VerifierTapeCleanup.totals e,
    max xs.length ys.length+1+1+t,?_,hr,?_,hei.trans hin,?_,?_⟩
  · change (d.work 7).head ≤ 1+_ at h7
    change (d.work 8).head ≤ 1+_ at h8
    omega
  · change (seqTM VerifierTotalsCompare.machine VerifierTapeCleanup.totals).halted _
    rw [phase2Wrap_halted_iff]; exact heh
  · change e.work = _
    rw [hew]
    funext j
    by_cases h8 : j = 8
    · subst j; simp [cleared]
    by_cases h7 : j = 7
    · subst j; simp [cleared]
    simpa only [cleared,Function.update_of_ne h8,Function.update_of_ne h7] using hframe j h7 h8
  · change e.output.HasBinaryPrefix _
    rw [heo]; exact hout

end UnconstrainedPACDetection.VerifierCompareReuse

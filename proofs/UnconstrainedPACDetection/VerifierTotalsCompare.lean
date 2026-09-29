module

public import proofs.UnconstrainedPACDetection.VerifierCompareFrame
public import proofs.UnconstrainedPACDetection.VerifierEntitySum

@[expose] public section

/-! Reuse the verified comparator on the two physical entity-total tapes. -/
namespace UnconstrainedPACDetection.VerifierTotalsCompare
open Complexity Complexity.TM

def buffered := retargetInput VerifierBinaryCompare.machine

theorem retarget_run {t : ℕ} {c d : Cfg 1 VerifierBinaryCompare.machine.Q}
    (h : VerifierBinaryCompare.machine.reachesIn t c d) (hi : c.input.StartInvariant)
    (realInput : Tape) (hr : realInput.read ≠ .start) :
    buffered.reachesIn t (retargetWrap VerifierBinaryCompare.machine realInput c)
      (retargetWrap VerifierBinaryCompare.machine realInput d) := by
  have hidle : realInput.move (idleDir realInput.read) = realInput := by simp [idleDir,hr,Tape.move]
  induction h with
  | zero => exact .zero
  | step hs _ ih =>
    have hc := input_cells_eq_of_step hs
    have hi' : _ := And.intro (hc ▸ hi.1) (fun j hj => hc ▸ hi.2 j hj)
    have hstep := retargetInput_step_commute VerifierBinaryCompare.machine hs realInput hi
    rw [hidle] at hstep
    exact .step hstep (ih hi')

def wiring : Equiv.Perm (Fin 11) where
  toFun := ![8,7,0,1,2,3,4,5,6,9,10]
  invFun := ![2,3,4,5,6,7,8,1,0,9,10]
  left_inv := by intro j; fin_cases j <;> rfl
  right_inv := by intro j; fin_cases j <;> rfl

def placed : TM 11 := placeWorkTM 0 9 buffered
def machine : TM 11 := VerifierWorkPermutation.machine placed wiring

theorem comparison_run (xs ys : List Bool) (c : Cfg 11 machine.Q)
    (hq : c.state = machine.qstart) (hx : (c.work 7).HasBinarySuffix xs)
    (hm : (c.work 7).StartInvariant) (hy : (c.work 8).HasBinarySuffix ys)
    (hf : ∀ j, j ≠ 7 → j ≠ 8 → (c.work j).read ≠ .start)
    (hi : c.input.read ≠ .start) (ho : c.output.HasBinaryPrefix []) :
    ∃ d, machine.reachesIn (max xs.length ys.length+1) c d ∧ machine.halted d ∧
      d.output.HasBinaryPrefix [VerifierBinaryCompare.compare false xs ys] ∧
      d.input = c.input ∧ (∀ j, j ≠ 7 → j ≠ 8 → d.work j = c.work j) := by
  let s : Cfg 1 VerifierBinaryCompare.machine.Q := ⟨c.state,c.work 7,![c.work 8],c.output⟩
  let extras : Fin 11 → Tape := fun j => c.work (wiring j)
  let embed := fun z : Cfg 1 VerifierBinaryCompare.machine.Q =>
    VerifierWorkPermutation.wrap placed wiring
      (placeWorkCfg buffered 0 9 extras (retargetWrap VerifierBinaryCompare.machine c.input z))
  have he : embed s = c := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  obtain ⟨d,hd,hh,hout⟩ := VerifierBinaryCompare.boundary xs ys false s hq hx hy [] ho
  have hb := retarget_run hd hm c.input hi
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal buffered 0 9 extras hb (by
    intro j hj
    have h0 : j ≠ 0 := by intro h; subst j; simp [placeWorkInMiddle] at hj
    have h1 : j ≠ 1 := by intro h; subst j; simp [placeWorkInMiddle] at hj
    apply hf (wiring j)
    · intro h; exact h1 (wiring.injective (show wiring j = wiring 1 from h))
    · intro h; exact h0 (wiring.injective (show wiring j = wiring 0 from h)))
  have hr := VerifierWorkPermutation.run_commute placed wiring hp
  refine ⟨embed d,?_,hh,?_,rfl,?_⟩
  · change machine.reachesIn _ (embed s) (embed d) at hr
    simpa only [he] using hr
  · exact hout
  · intro j h7 h8
    fin_cases j
    all_goals first | exact False.elim (h7 rfl) | exact False.elim (h8 rfl) | rfl

theorem comparison_frame (xs ys : List Bool) (c : Cfg 11 machine.Q)
    (hq : c.state = machine.qstart) (hx : (c.work 7).HasBinarySuffix xs)
    (hm : (c.work 7).StartInvariant) (hy : (c.work 8).HasBinarySuffix ys)
    (hf : ∀ j, j ≠ 7 → j ≠ 8 → (c.work j).read ≠ .start)
    (hi : c.input.read ≠ .start) (ho : c.output.HasBinaryPrefix []) :
    ∃ d, machine.reachesIn (max xs.length ys.length+1) c d ∧ machine.halted d ∧
      d.output.HasBinaryPrefix [VerifierBinaryCompare.compare false xs ys] ∧
      d.input = c.input ∧ (∀ j, j ≠ 7 → j ≠ 8 → d.work j = c.work j) ∧
      (d.work 7).HasBinarySuffix [] ∧ (d.work 8).HasBinarySuffix [] ∧
      (d.work 7).cells = (c.work 7).cells ∧ (d.work 8).cells = (c.work 8).cells := by
  let s : Cfg 1 VerifierBinaryCompare.machine.Q := ⟨c.state,c.work 7,![c.work 8],c.output⟩
  let extras : Fin 11 → Tape := fun j => c.work (wiring j)
  let embed := fun z : Cfg 1 VerifierBinaryCompare.machine.Q =>
    VerifierWorkPermutation.wrap placed wiring
      (placeWorkCfg buffered 0 9 extras (retargetWrap VerifierBinaryCompare.machine c.input z))
  have he : embed s = c := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  obtain ⟨d,hd,hh,hout,hxe,hye,hxc,hyc⟩ := VerifierBinaryCompare.boundary_frame xs ys false s hq hx hy [] ho
  have hb := retarget_run hd hm c.input hi
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal buffered 0 9 extras hb (by
    intro j hj
    have h0 : j ≠ 0 := by intro h; subst j; simp [placeWorkInMiddle] at hj
    have h1 : j ≠ 1 := by intro h; subst j; simp [placeWorkInMiddle] at hj
    apply hf (wiring j)
    · intro h; exact h1 (wiring.injective (show wiring j = wiring 1 from h))
    · intro h; exact h0 (wiring.injective (show wiring j = wiring 0 from h)))
  have hr := VerifierWorkPermutation.run_commute placed wiring hp
  refine ⟨embed d,?_,hh,?_,rfl,?_,hxe,hye,hxc,hyc⟩
  · change machine.reachesIn _ (embed s) (embed d) at hr
    simpa only [he] using hr
  · exact hout
  · intro j h7 h8
    fin_cases j
    all_goals first | exact False.elim (h7 rfl) | exact False.elim (h8 rfl) | rfl

end UnconstrainedPACDetection.VerifierTotalsCompare

module

public import proofs.UnconstrainedPACDetection.VerifierWorkPermutation
public import proofs.UnconstrainedPACDetection.VerifierBufferedAccumulate
public import proofs.UnconstrainedPACDetection.VerifierFieldPlacement

@[expose] public section

/-! Product5 can be accumulated into either total7 or total8 in place. -/
namespace UnconstrainedPACDetection.VerifierTotalBranch
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)

def target (positive : Bool) : Fin 9 := if positive then 7 else 8
def wiring (positive : Bool) : Equiv.Perm (Fin 9) where
  toFun := if positive then ![7,5,0,1,2,3,4,6,8] else ![8,5,0,1,2,3,4,6,7]
  invFun := if positive then ![2,3,4,5,6,1,7,0,8] else ![2,3,4,5,6,1,7,8,0]
  left_inv := by intro j; cases positive <;> fin_cases j <;> rfl
  right_inv := by intro j; cases positive <;> fin_cases j <;> rfl
def placed : TM 9 := placeWorkTM 0 7 VerifierBufferedAccumulate.machine
def machine (positive : Bool) : TM 9 := VerifierWorkPermutation.machine placed (wiring positive)

theorem accumulation_run (positive : Bool) (term total : List Bool)
    (c : Cfg 9 (machine positive).Q) (hq : c.state = (machine positive).qstart)
    (hp : (c.work 5).HasBinaryString term) (hpm : (c.work 5).StartInvariant)
    (ht : (c.work (target positive)).HasBinaryString total)
    (htm : (c.work (target positive)).cells 0 = .start)
    (hf : ∀ j, j ≠ target positive → j ≠ 5 → (c.work j).read ≠ .start)
    (hi : c.input.read ≠ .start) (ho : c.output.read ≠ .start) :
    ∃ d, (machine positive).reachesIn
        (max term.length total.length+term.length+(VerifierBinaryAdd.add false term total).length+5) c d ∧
      (machine positive).halted d ∧
      d.work = Function.update c.work (target positive) (wordTape (VerifierBinaryAdd.add false term total)) ∧
      d.input = c.input ∧ d.output = c.output := by
  let s : Cfg 2 VerifierBufferedAccumulate.machine.Q :=
    ⟨c.state, c.input, ![c.work (target positive), c.work 5], c.output⟩
  let extras : Fin 9 → Tape := fun j => c.work (wiring positive j)
  let embed := fun z : Cfg 2 VerifierBufferedAccumulate.machine.Q =>
    VerifierWorkPermutation.wrap placed (wiring positive)
      (placeWorkCfg VerifierBufferedAccumulate.machine 0 7 extras z)
  have he : embed s = c := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      cases positive <;> fin_cases j <;>
        simp [embed, VerifierWorkPermutation.wrap, wiring, target, placeWorkCfg,
          placeWorkInMiddle, placeWorkCoord, extras, s]
    · rfl
  obtain ⟨d,hd,hh,hp',hz,hterm,hin,hout⟩ :=
    VerifierBufferedAccumulate.accumulation_run term total s hq hp hpm ht htm hi ho
  have hplaced := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierBufferedAccumulate.machine 0 7 extras hd (by
      intro j hj
      have h0 : j ≠ 0 := by intro h; subst j; simp [placeWorkInMiddle] at hj
      have h1 : j ≠ 1 := by intro h; subst j; simp [placeWorkInMiddle] at hj
      have w0 : wiring positive 0 = target positive := by cases positive <;> rfl
      have w1 : wiring positive 1 = 5 := by cases positive <;> rfl
      apply hf (wiring positive j)
      · intro h
        exact h0 ((wiring positive).injective (h.trans w0.symm))
      · intro h
        exact h1 ((wiring positive).injective (h.trans w1.symm)))
  have hrun := VerifierWorkPermutation.run_commute placed (wiring positive) hplaced
  have hw : d.work 0 = wordTape (VerifierBinaryAdd.add false term total) :=
    Tape.eq_init_move_right_of_hasBinaryString hp' hz
  refine ⟨embed d, ?_, hh, ?_, hin, hout⟩
  · change (machine positive).reachesIn _ (embed s) (embed d) at hrun
    simpa only [he] using hrun
  · funext j
    cases positive <;> fin_cases j <;>
      simp [embed, VerifierWorkPermutation.wrap, wiring, target, placeWorkCfg,
        placeWorkInMiddle, placeWorkCoord, extras, s, hw, hterm]

end UnconstrainedPACDetection.VerifierTotalBranch

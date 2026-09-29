module

public import proofs.UnconstrainedPACDetection.VerifierWorkPermutation
public import proofs.UnconstrainedPACDetection.VerifierBufferedProduct
public import proofs.Complexitylib.Models.TuringMachine.Placement.Internal

@[expose] public section

/-! Multiply the coefficient and magnitude where signed extraction leaves them. -/
namespace UnconstrainedPACDetection.VerifierSelectedProduct
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)

def wiring : Equiv.Perm (Fin 7) where
  toFun := ![2,5,6,0,1,3,4]
  invFun := ![3,4,0,5,6,1,2]
  left_inv := by intro j; fin_cases j <;> rfl
  right_inv := by intro j; fin_cases j <;> rfl

def placed : TM 7 := placeWorkTM 0 3 VerifierBufferedProduct.machine
def machine : TM 7 := VerifierWorkPermutation.machine placed wiring

/-- Physical coefficient0 and magnitude2 are multiplied into product5.
Index1/sign3/witness4 and all caller tapes are preserved exactly. -/
theorem multiplication_run (xs ys : List Bool) (c : Cfg 7 machine.Q)
    (hq : c.state = machine.qstart)
    (hx : (c.work 0).HasBinaryString xs) (hxm : (c.work 0).StartInvariant)
    (hy : (c.work 2).HasBinaryString ys) (hym : (c.work 2).StartInvariant)
    (hp : c.work 5 = wordTape []) (ht : c.work 6 = wordTape [])
    (hf : ∀ j : Fin 7, j = 1 ∨ j = 3 ∨ j = 4 → (c.work j).read ≠ .start)
    (hi : c.input.read ≠ .start) (ho : c.output.read ≠ .start) :
    ∃ t d, t ≤ ys.length+2+ys.length*(10*xs.length+20*ys.length+30) ∧
      machine.reachesIn t c d ∧ machine.halted d ∧
      d.work = Function.update c.work 5 (wordTape (VerifierBinaryProduct.multiply xs ys)) ∧
      d.input = c.input ∧ d.output = c.output := by
  let s : Cfg 4 VerifierBufferedProduct.machine.Q :=
    ⟨c.state, c.input, ![c.work 2, c.work 5, c.work 6, c.work 0], c.output⟩
  let extras : Fin 7 → Tape := fun j => c.work (wiring j)
  let embed := fun z : Cfg 4 VerifierBufferedProduct.machine.Q =>
    VerifierWorkPermutation.wrap placed wiring
      (placeWorkCfg VerifierBufferedProduct.machine 0 3 extras z)
  have he : embed s = c := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [embed, VerifierWorkPermutation.wrap, wiring, placeWorkCfg,
        placeWorkInMiddle, placeWorkCoord, extras, s]
    · rfl
  obtain ⟨t,d,hb,hd,hh,hprod,hm,hxs,hys,htemp,hin,hout⟩ :=
    VerifierBufferedProduct.multiplication_run xs ys s hq hx hxm hy hym hp ht hi ho
  have hplaced := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierBufferedProduct.machine 0 3 extras hd (by
      intro j hj
      fin_cases j
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · exact hf 1 (Or.inl rfl)
      · exact hf 3 (Or.inr (Or.inl rfl))
      · exact hf 4 (Or.inr (Or.inr rfl)))
  have hrun := VerifierWorkPermutation.run_commute placed wiring hplaced
  have hw : d.work 1 = wordTape (VerifierBinaryProduct.multiply xs ys) :=
    Tape.eq_init_move_right_of_hasBinaryString hprod hm.1
  refine ⟨t, embed d, hb, ?_, hh, ?_, hin, hout⟩
  · change machine.reachesIn t (embed s) (embed d) at hrun
    simpa only [he] using hrun
  · funext j
    fin_cases j <;> simp [embed, VerifierWorkPermutation.wrap, wiring, placeWorkCfg,
      placeWorkInMiddle, placeWorkCoord, extras, hw, hxs, hys, htemp, s, ht]
    rfl

end UnconstrainedPACDetection.VerifierSelectedProduct

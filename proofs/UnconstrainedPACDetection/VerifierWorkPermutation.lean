module

public import proofs.Complexitylib.Models.TuringMachine
public import Mathlib.Tactic

@[expose] public section

/-! Actual transition-table permutation for connecting verifier subroutines.
No tape contents are copied: the finite machine addresses different slots. -/
namespace UnconstrainedPACDetection.VerifierWorkPermutation
open Complexity
open Complexity.TM

def machine {n : ℕ} (M : TM n) (σ : Equiv.Perm (Fin n)) : TM n where
  Q := M.Q
  qstart := M.qstart
  qhalt := M.qhalt
  δ := fun q i w o =>
    let r := M.δ q i (fun j => w (σ j)) o
    (r.1, fun j => r.2.1 (σ.symm j), r.2.2.1, r.2.2.2.1,
      fun j => r.2.2.2.2.1 (σ.symm j), r.2.2.2.2.2)
  δ_right_of_start := by
    intro q i w o
    obtain ⟨hi, hw, ho⟩ := M.δ_right_of_start q i (fun j => w (σ j)) o
    refine ⟨hi, fun j hj => ?_, ho⟩
    apply hw (σ.symm j)
    simpa only [Equiv.apply_symm_apply] using hj

def wrap {n : ℕ} (M : TM n) (σ : Equiv.Perm (Fin n)) (c : Cfg n M.Q) :
    Cfg n (machine M σ).Q := ⟨c.state, c.input, fun j => c.work (σ.symm j), c.output⟩

theorem step_commute {n : ℕ} (M : TM n) (σ : Equiv.Perm (Fin n)) (c : Cfg n M.Q) :
    (machine M σ).step (wrap M σ c) = (M.step c).map (wrap M σ) := by
  simp only [TM.step, machine, wrap, Equiv.symm_apply_apply]
  split <;> rfl

theorem run_commute {n : ℕ} (M : TM n) (σ : Equiv.Perm (Fin n))
    {t : ℕ} {c d : Cfg n M.Q} (h : M.reachesIn t c d) :
    (machine M σ).reachesIn t (wrap M σ c) (wrap M σ d) := by
  induction h with
  | zero => exact .zero
  | @step c _ _ _ hs _ ih =>
    exact .step (by simpa only [hs, Option.map_some] using step_commute M σ c) ih

end UnconstrainedPACDetection.VerifierWorkPermutation

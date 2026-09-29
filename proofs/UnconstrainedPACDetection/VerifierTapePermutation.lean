module

public import proofs.UnconstrainedPACDetection.VerifierMaskAccess

@[expose] public section

/-! Tape relabeling for placing the mask reader on the existing entity layout.
No simulation overhead or extra storage is introduced. -/
namespace UnconstrainedPACDetection.VerifierTapePermutation
open Complexity Complexity.TM
variable {n : ℕ}

def machine (tm : TM n) (e : Equiv.Perm (Fin n)) : TM n where
  Q := tm.Q
  qstart := tm.qstart
  qhalt := tm.qhalt
  δ := fun q i w o =>
    let a := tm.δ q i (fun j => w (e j)) o
    (a.1,fun j => a.2.1 (e.symm j),a.2.2.1,a.2.2.2.1,
      fun j => a.2.2.2.2.1 (e.symm j),a.2.2.2.2.2)
  δ_right_of_start := by
    intro q i w o
    obtain ⟨hi,hw,ho⟩ := tm.δ_right_of_start q i (fun j => w (e j)) o
    exact ⟨hi,fun j h => hw (e.symm j) (by simpa using h),ho⟩

def wrap (tm : TM n) (e : Equiv.Perm (Fin n)) (c : Cfg n tm.Q) : Cfg n tm.Q :=
  ⟨c.state,c.input,fun j => c.work (e.symm j),c.output⟩

theorem step (tm : TM n) (e : Equiv.Perm (Fin n)) (c : Cfg n tm.Q) :
    (machine tm e).step (wrap tm e c) = (tm.step c).map (wrap tm e) := by
  by_cases hh : c.state = tm.qhalt
  · simp [TM.step,machine,wrap,hh]
  · simp [TM.step,machine,wrap,hh]

theorem run (tm : TM n) (e : Equiv.Perm (Fin n)) {t : ℕ} {c d : Cfg n tm.Q}
    (h : tm.reachesIn t c d) :
    (machine tm e).reachesIn t (wrap tm e c) (wrap tm e d) := by
  induction h with
  | zero => exact .zero
  | step hs _ ih => exact .step (by rw [step,hs]; rfl) ih

end UnconstrainedPACDetection.VerifierTapePermutation

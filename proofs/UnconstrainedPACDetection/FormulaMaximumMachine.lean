module

public import proofs.UnconstrainedPACDetection.FormulaMaximumTape

@[expose] public section

namespace UnconstrainedPACDetection.FormulaMaximum
open Complexity Complexity.TM

inductive Phase where
  | scanning (q : ScanState) | rewind | done
  deriving DecidableEq, Fintype

def machine : TM 1 where
  Q := Phase
  qstart := .scanning (false,none)
  qhalt := .done
  δ := fun q i w o =>
    match q with
    | .done => allIdle .done i w o
    | .rewind =>
      (if w 0 = .start then .scanning (false,none) else .rewind,
        fun j => readBackWrite (w j),readBackWrite o,idleDir i,
        fun j => if w j = .start then .right else .left,idleDir o)
    | .scanning s =>
      if i = .start then
        (.scanning s,fun j => readBackWrite (w j),readBackWrite o,
          .right,fun j => idleDir (w j),idleDir o)
      else if i = .blank then
        (.done,fun j => readBackWrite (w j),readBackWrite o,
          idleDir i,fun j => idleDir (w j),idleDir o)
      else match action s (decide (i = .one)) with
      | .keep s' => (.scanning s',fun j => readBackWrite (w j),readBackWrite o,
          .right,fun j => idleDir (w j),idleDir o)
      | .advance => (.scanning (true,none),fun _ => .one,
          if w 0 = .blank then .one else readBackWrite o,
          .right,fun _ => .right,if w 0 = .blank then .right else idleDir o)
      | .reset => (.rewind,fun j => readBackWrite (w j),readBackWrite o,
          .right,fun j => idleDir (w j),idleDir o)
  δ_right_of_start := by
    intro q i w o
    cases q with
    | done => exact rightOfStart_allIdle i w o
    | rewind =>
      exact ⟨idleDir_right_of_start,fun j h => by simp [h],idleDir_right_of_start⟩
    | scanning s =>
      dsimp only
      split
      · exact ⟨fun _ => rfl,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
      · split
        · exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
        · split
          · exact ⟨fun _ => rfl,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
          · refine ⟨fun _ => rfl,fun _ _ => rfl,?_⟩
            split
            · exact fun _ => rfl
            · exact idleDir_right_of_start
          · exact ⟨fun _ => rfl,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩

def cfg (q : Phase) (inp out : Tape) (mx head : Nat) : Cfg 1 machine.Q :=
  ⟨q,inp,fun _ => ⟨head,regCells mx⟩,out⟩

theorem rewind_run (head mx : Nat) (inp out : Tape)
    (hi : inp.read ≠ .start) (ho : out.read ≠ .start) :
    machine.reachesIn (head+1) (cfg .rewind inp out mx head)
      (cfg (.scanning (false,none)) inp out mx 1) := by
  induction head with
  | zero =>
    have hs : machine.step (cfg .rewind inp out mx 0) =
        some (cfg (.scanning (false,none)) inp out mx 1) := by
      simp [TM.step,machine,cfg,Tape.read,regCells_zero]
      refine ⟨?_,?_,transitionTape_eq_self ho⟩
      · simpa only [Tape.read] using (show inp.move (idleDir inp.read) = inp by simp [idleDir,hi,Tape.move])
      · funext j
        simp [Tape.writeAndMove,Tape.write,Tape.move]
    exact .step hs .zero
  | succ h ih =>
    have hr : (⟨h+1,regCells mx⟩ : Tape).read ≠ .start := by
      change regCells mx (h+1) ≠ .start
      exact regCells_ne_start (by omega)
    have hs : machine.step (cfg .rewind inp out mx (h+1)) =
        some (cfg .rewind inp out mx h) := by
      have hc : regCells mx (h+1) ≠ .start := hr
      simp only [TM.step,machine,cfg,reduceCtorEq,↓reduceIte,Tape.read,ite_eq_right hc]
      congr 1
      apply Cfg.ext
      · rfl
      · change inp.move (idleDir inp.read) = inp
        simp [idleDir,hi,Tape.move]
      · funext j
        change ((⟨h+1,regCells mx⟩ : Tape).write (readBackWrite _).toΓ).move .left = _
        have hb := write_back (⟨h+1,regCells mx⟩ : Tape) hr
        simpa [Tape.read,Tape.move] using congrArg (fun t : Tape => t.move .left) hb
      · exact transitionTape_eq_self ho
    exact .step hs ih

end UnconstrainedPACDetection.FormulaMaximum

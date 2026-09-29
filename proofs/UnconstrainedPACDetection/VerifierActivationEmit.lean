module

public import proofs.UnconstrainedPACDetection.VerifierActivationRow

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationEmit
open Complexity Complexity.TM
open VerifierVerdictAnd (one empty)
open VerifierAccumulate (markerDir)

def machine : TM 1 where
  Q := Fin 3
  qstart := 0
  qhalt := 2
  δ := fun q i w o =>
    if q = 0 then
      (1,fun j => readBackWrite (w j),readBackWrite o,idleDir i,
        fun j => markerDir (w j) .left,idleDir o)
    else
      (2,fun _ => .blank,readBackWrite (w 0),idleDir i,
        fun j => idleDir (w j),.right)
  δ_right_of_start := by
    intro q i w o
    by_cases hq : q = 0
    · simp only [hq,↓reduceIte]
      exact ⟨idleDir_right_of_start,fun _ h => by simp [markerDir,h],idleDir_right_of_start⟩
    · simp only [hq,↓reduceIte]
      exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,fun _ => True.intro⟩

theorem run (inp out : Tape) (hi : inp.read ≠ .start) (ho : out.read ≠ .start)
    (m : Γ) (v : Bool) :
    machine.reachesIn 2 ⟨(0 : Fin 3),inp,fun _ => one m v,out⟩
      ⟨(2 : Fin 3),inp,fun _ => empty m,out.writeAndMove (Γ.ofBool v) .right⟩ := by
  let mid : Cfg 1 (Fin 3) := ⟨1,inp,fun _ => {one m v with head := 1},out⟩
  have h1 : machine.step ⟨(0 : Fin 3),inp,fun _ => one m v,out⟩ = some mid := by
    have hir : inp.cells inp.head ≠ .start := hi
    simp only [TM.step,machine,↓reduceIte]
    simp only [show (0 : Fin 3) ≠ 2 by decide,↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · simp [idleDir,hir,Tape.read,Tape.move,mid]
    · funext j
      change (one m v).writeAndMove .blank .left = {one m v with head := 1}
      apply Tape.ext
      · rfl
      · funext i
        by_cases h : i = 2 <;> simp [Tape.writeAndMove,Tape.write,Tape.move,one,h,Function.update]
    · exact transitionTape_eq_self ho
  have h2 : machine.step mid = some
      ⟨(2 : Fin 3),inp,fun _ => empty m,out.writeAndMove (Γ.ofBool v) .right⟩ := by
    have hir : inp.cells inp.head ≠ .start := hi
    cases v <;>
      simp [TM.step,machine,mid,Tape.read,one,idleDir,hir,Γ.ofBool,readBackWrite,
        Tape.writeAndMove,Tape.write,Tape.move,empty]
    all_goals
      funext j
      apply Tape.ext
      · rfl
      · funext i
        by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp_all [Function.update]
  exact .step h1 (.step h2 .zero)

theorem emits (inp out : Tape) (hi : inp.read ≠ .start) (m : Γ) (v : Bool)
    (bits : List Bool) (ho : out.HasBinaryPrefix bits) :
    ∃ d, machine.reachesIn 2 ⟨(0 : Fin 3),inp,fun _ => one m v,out⟩ d ∧
      d.state = (2 : Fin 3) ∧ d.input = inp ∧ d.work = (fun _ => empty m) ∧
      d.output.HasBinaryPrefix (bits ++ [v]) := by
  exact ⟨_,run inp out hi (by rw [ho.read_blank]; decide) m v,rfl,rfl,rfl,
    Tape.hasBinaryPrefix_write_bit v ho⟩

def seed : TM 1 where
  Q := Fin 2
  qstart := 0
  qhalt := 1
  δ := fun _ i w o => (1,fun _ => .zero,readBackWrite o,idleDir i,
    fun j => markerDir (w j) .stay,idleDir o)
  δ_right_of_start := by
    intro q i w o
    exact ⟨idleDir_right_of_start,fun _ h => by simp [markerDir,h],idleDir_right_of_start⟩

theorem seed_run (inp out : Tape) (hi : inp.read ≠ .start) (ho : out.read ≠ .start) (m : Γ) :
    seed.reachesIn 1 ⟨(0 : Fin 2),inp,fun _ => empty m,out⟩
      ⟨(1 : Fin 2),inp,fun _ => VerifierActivationScan.flag m false,out⟩ := by
  refine .step ?_ .zero
  simp only [TM.step,seed,show (0 : Fin 2) ≠ 1 by decide,↓reduceIte]
  congr 1
  apply Cfg.ext
  · rfl
  · exact transitionInput_eq_self hi
  · funext j
    change (empty m).writeAndMove .zero .stay = VerifierActivationScan.flag m false
    apply Tape.ext
    · rfl
    · funext i
      by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
        simp [Tape.writeAndMove,Tape.write,Tape.move,empty,VerifierActivationScan.flag,one,Γ.ofBool,h0,h1]
  · exact transitionTape_eq_self ho

end UnconstrainedPACDetection.VerifierActivationEmit

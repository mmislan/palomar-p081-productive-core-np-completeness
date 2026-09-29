module

public import proofs.UnconstrainedPACDetection.VerifierOutputRouting

@[expose] public section

namespace UnconstrainedPACDetection.VerifierVerdictAnd
open Complexity Complexity.TM
open VerifierAccumulate (markerDir)

def one (marker : Γ) (b : Bool) : Tape :=
  ⟨2,fun i => if i = 0 then marker else if i = 1 then Γ.ofBool b else .blank⟩
def empty (marker : Γ) : Tape := ⟨1,fun i => if i = 0 then marker else .blank⟩

theorem prefix_eq (t : Tape) (b : Bool) (h : t.HasBinaryPrefix [b]) : t = one (t.cells 0) b := by
  apply Tape.ext
  · simpa [one] using h.1
  · funext i
    by_cases h0 : i = 0
    · subst i; simp [one]
    by_cases h1 : i = 1
    · subst i; simpa [one] using h.2.1 0 (by simp)
    have hi : i-1+1 = i := by omega
    have ht := h.2.2 (i-1) (by simp; omega)
    simpa [one,h0,h1,hi] using ht

def machine : TM 1 where
  Q := Fin 3
  qstart := 0
  qhalt := 2
  δ := fun q i w o =>
    if q = 0 then
      (1,fun j => readBackWrite (w j),readBackWrite o,idleDir i,
        fun j => markerDir (w j) .left,markerDir o .left)
    else
      (2,fun _ => .blank,readBackWrite (Γ.ofBool (decide (w 0 = .one) && decide (o = .one))),
        idleDir i,fun j => idleDir (w j),.right)
  δ_right_of_start := by
    intro q i w o
    by_cases hq : q = 0
    · simp only [hq,↓reduceIte]
      exact ⟨idleDir_right_of_start,fun _ h => by simp [markerDir,h],fun h => by simp [markerDir,h]⟩
    · simp only [hq,↓reduceIte]
      exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,fun _ => True.intro⟩

theorem write_one (m : Γ) (a b : Bool) :
    ({one m a with head := 1} : Tape).writeAndMove (Γ.ofBool b) .right = one m b := by
  apply Tape.ext
  · rfl
  · funext i
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
      simp [Tape.writeAndMove,Tape.write,Tape.move,one,h0,h1]

theorem clear_one (m : Γ) (b : Bool) :
    ({one m b with head := 1} : Tape).writeAndMove .blank .stay = empty m := by
  apply Tape.ext
  · rfl
  · funext i
    by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
      simp [Tape.writeAndMove,Tape.write,Tape.move,one,empty,h0,h1]

theorem run (inp : Tape) (hi : inp.read ≠ .start) (sm om : Γ) (v a : Bool) :
    machine.reachesIn 2 ⟨(0 : Fin 3),inp,fun _ => one sm v,one om a⟩
      ⟨(2 : Fin 3),inp,fun _ => empty sm,one om (v && a)⟩ := by
  let mid : Cfg 1 machine.Q :=
    ⟨(1 : Fin 3),inp,fun _ => {one sm v with head := 1},{one om a with head := 1}⟩
  have h1 : machine.step ⟨(0 : Fin 3),inp,fun _ => one sm v,one om a⟩ = some mid := by
    have hir : inp.cells inp.head ≠ .start := hi
    simp [TM.step,machine,mid,one,Tape.read,Tape.writeAndMove,Tape.write,Tape.move,
      markerDir,idleDir,hir,readBackWrite]
    funext j
    apply Tape.ext
    · rfl
    · funext i
      by_cases h : i = 2 <;> simp_all [Function.update]
  have h2 : machine.step mid = some ⟨(2 : Fin 3),inp,fun _ => empty sm,one om (v && a)⟩ := by
    have hir : inp.cells inp.head ≠ .start := hi
    cases v <;> cases a <;>
      simp [TM.step,machine,mid,Tape.read,one,idleDir,hir,Γ.ofBool,readBackWrite,
        Tape.writeAndMove,Tape.write,Tape.move,empty]
    all_goals try constructor
    all_goals
      funext i
      by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp_all [Function.update]
    all_goals
      funext cell
      by_cases hz : cell = 0 <;> by_cases ho : cell = 1 <;> simp_all [Function.update]
  exact .step h1 (.step h2 .zero)

end UnconstrainedPACDetection.VerifierVerdictAnd

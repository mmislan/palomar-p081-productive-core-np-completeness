module

public import proofs.UnconstrainedPACDetection.VerifierSourceRegisters

@[expose] public section

namespace UnconstrainedPACDetection.VerifierSourceHeaderGuard
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierAccumulate (markerDir)
open VerifierWitnessRegisters (pair)

inductive Phase where
  | first | second (present : Bool) | done
  deriving DecidableEq, Fintype

def gate : TM 2 where
  Q := Phase
  qstart := .first
  qhalt := .done
  δ := fun q i w o => match q with
    | .first =>
      (.second (decide (w 0 = .one)),fun j => readBackWrite (w j),readBackWrite o,
        idleDir i,fun j => if j = 0 ∧ w 0 = .one then .right else idleDir (w j),markerDir o .left)
    | .second present =>
      (.done,fun j => readBackWrite (w j),
        readBackWrite (Γ.ofBool (present && decide (w 0 = .one) && decide (o = .one))),
        idleDir i,fun j => if j = 0 ∧ present = true then markerDir (w j) .left else idleDir (w j),.right)
    | .done => allIdle .done i w o
  δ_right_of_start := by
    intro q i w o
    cases q with
    | first =>
      refine ⟨idleDir_right_of_start,?_,fun h => by simp [markerDir,h]⟩
      intro j h
      dsimp only
      split
      · rfl
      · exact idleDir_right_of_start h
    | second b =>
      refine ⟨idleDir_right_of_start,?_,fun _ => rfl⟩
      intro j h
      dsimp only
      split
      · simp [markerDir,h]
      · exact idleDir_right_of_start h
    | done => exact rightOfStart_allIdle i w o

def unary (n : ℕ) := wordTape (List.replicate n true)

theorem gate_run (n : ℕ) (b : Bool) (inp : Tape) (hi : inp.read ≠ .start) :
    gate.reachesIn 2 ⟨.first,inp,pair (unary n) (wordTape []),one .start b⟩
      ⟨.done,inp,pair (unary n) (wordTape []),one .start (decide (2 ≤ n) && b)⟩ := by
  have hir : inp.cells inp.head ≠ .start := hi
  let mid : Cfg 2 Phase := ⟨.second (decide (0 < n)),inp,
    pair {unary n with head := if 0 < n then 2 else 1} (wordTape []),
    {one .start b with head := 1}⟩
  have h1 : gate.step ⟨.first,inp,pair (unary n) (wordTape []),one .start b⟩ = some mid := by
    cases n <;> cases b <;> simp [TM.step,gate,mid,pair,unary,wordTape,one,Tape.read,Tape.init,
      Tape.move,Tape.writeAndMove,Tape.write,markerDir,idleDir,hir,readBackWrite,Γ.ofBool,List.replicate_succ]
    all_goals
      funext j
      fin_cases j <;> simp
  have h2 : gate.step mid = some
      ⟨.done,inp,pair (unary n) (wordTape []),one .start (decide (2 ≤ n) && b)⟩ := by
    rcases n with _ | (_ | n)
    all_goals
      cases b <;> simp [TM.step,gate,mid,pair,unary,wordTape,one,Tape.read,Tape.init,
        Tape.move,Tape.writeAndMove,Tape.write,markerDir,idleDir,hir,readBackWrite,Γ.ofBool,List.replicate_succ]
    all_goals try constructor
    all_goals
      first
      | (funext j; fin_cases j <;> simp)
      | (funext i; by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp_all [Function.update])
  exact .step h1 (.step h2 .zero)

end UnconstrainedPACDetection.VerifierSourceHeaderGuard

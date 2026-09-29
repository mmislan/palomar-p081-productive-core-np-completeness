module

public import proofs.IrrRAFEnumeration.SATMachineEmit

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

/-- Emit a register-sized constant run using a fixed-state loop, not an
input-sized unrolling of the machine's control graph. -/
def emitRunTM {k : Nat} (b : Bool) (r : Fin k) : TM k :=
  forRegTM (emitBitsTM [b]) r

theorem emitRunTM_correct {k : Nat} (b : Bool) (r : Fin k) (v : Nat)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hip : Parked inp) (hwp : ∀ i, Parked (work i)) (hr : work r = regTape v) :
    (emitRunTM b r).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys ++ List.replicate v b)) (4*v+2) := by
  have hbody : ∀ i, i < v → (emitBitsTM (n := k) [b]).HoareTime
      (EmitPred inp (Function.update work r ⟨i+2,regCells v⟩)
        (ys ++ List.replicate i b))
      (EmitPred inp (Function.update work r ⟨i+2,regCells v⟩)
        (ys ++ List.replicate (i+1) b)) 1 := by
    intro i _
    have hw : ∀ j, Parked (Function.update work r ⟨i+2,regCells v⟩ j) := by
      intro j
      by_cases hj : j = r
      · subst j
        rw [Function.update_self]
        exact ⟨by dsimp; omega, fun _ h => regCells_ne_start h⟩
      · rw [Function.update_of_ne hj]
        exact hwp j
    unfold EmitPred
    simpa only [List.length_singleton, List.replicate_succ', List.append_assoc] using
      emitBitsTM_hoareTime [b] inp _ (ys ++ List.replicate i b) hip hw
  have h := forRegTM_hoareTime (emitBitsTM [b]) r v inp
    (fun _ => work) (fun i => ys ++ List.replicate i b) 1 hip
    (fun _ => hr) (fun _ j _ => hwp j) hbody
  have he : v*(1+2)+(v+2) = 4*v+2 := by omega
  simpa only [emitRunTM, List.replicate_zero, List.append_nil, he] using h

end IrrRAFEnumeration.SATSource

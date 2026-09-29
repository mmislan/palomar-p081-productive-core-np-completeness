module

public import proofs.IrrRAFEnumeration.SATRowMachines

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

/-- Copy a false-terminated unary header into an empty register and rewind
that register. The input is left immediately after the delimiter. -/
def headerRegTM {k : Nat} (q : Fin k) : TM k where
  Q := IncPhase
  qstart := .scan
  qhalt := .done
  δ := fun s ih wh oh => match s with
    | .scan => if ih = Γ.one then
        (.scan, fun i => if i = q then Γw.one else readBackWrite (wh i),
          readBackWrite oh, Dir3.right,
          fun i => if i = q then Dir3.right else idleDir (wh i), idleDir oh)
      else
        (.back, fun i => readBackWrite (wh i), readBackWrite oh, Dir3.right,
          fun i => if i = q then (if wh q = Γ.start then Dir3.right else Dir3.left)
            else idleDir (wh i), idleDir oh)
    | .back =>
        (if wh q = Γ.start then .done else .back,
          fun i => readBackWrite (wh i), readBackWrite oh, idleDir ih,
          fun i => if i = q then (if wh q = Γ.start then Dir3.right else Dir3.left)
            else idleDir (wh i), idleDir oh)
    | s => allIdle s ih wh oh
  δ_right_of_start := by
    intro s ih wh oh
    cases s <;> simp only []
    · split
      · refine ⟨fun _ => rfl, ?_, idleDir_right_of_start⟩
        intro i hi
        by_cases he : i = q
        · simp [he]
        · simp [he, idleDir_right_of_start hi]
      · refine ⟨fun _ => rfl, ?_, idleDir_right_of_start⟩
        intro i hi
        by_cases he : i = q
        · subst i; simp [hi]
        · simp [he, idleDir_right_of_start hi]
    · refine ⟨idleDir_right_of_start, ?_, idleDir_right_of_start⟩
      intro i hi
      by_cases he : i = q
      · subst i; simp [hi]
      · simp [he, idleDir_right_of_start hi]
    · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
    · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩

theorem header_scan_step {k : Nat} (q : Fin k) (inp : Tape)
    (work : Fin k → Tape) (out : Tape) (i : Nat)
    (hi : inp.read = Γ.one) (hw : ∀ j, Parked (work j)) (ho : Parked out) :
    (headerRegTM q).step
      {state := .scan, input := inp,
       work := Function.update work q ⟨i+1,regCells i⟩, output := out} = some
      {state := .scan, input := inp.move .right,
       work := Function.update work q ⟨i+2,regCells (i+1)⟩, output := out} := by
  simp only [TM.step, headerRegTM, reduceCtorEq, ↓reduceIte, hi]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl,rfl,?_,ho.writeAndMove_readBack_idle⟩)
  funext j
  by_cases hj : j = q
  · subst j
    simp only [Function.update_self, ↓reduceIte]
    apply Tape.ext
    · rfl
    · simp only [Tape.writeAndMove, Tape.move_cells, Tape.write, show i+1 ≠ 0 by omega,
        ↓reduceIte]
      exact regCells_update_succ i
  · simp only [hj, ↓reduceIte, Function.update_of_ne hj]
    exact (hw j).writeAndMove_readBack_idle

theorem header_delimiter_step {k : Nat} (q : Fin k) (inp : Tape)
    (work : Fin k → Tape) (out : Tape) (v : Nat)
    (hi : inp.read = Γ.zero) (hw : ∀ j, Parked (work j)) (ho : Parked out) :
    (headerRegTM q).step
      {state := .scan, input := inp,
       work := Function.update work q ⟨v+1,regCells v⟩, output := out} = some
      {state := .back, input := inp.move .right,
       work := Function.update work q ⟨v,regCells v⟩, output := out} := by
  have hr : (⟨v+1,regCells v⟩ : Tape).read = Γ.blank := by
    change regCells v (v+1) = Γ.blank
    exact regCells_blank (by omega)
  simp only [TM.step, headerRegTM, reduceCtorEq, ↓reduceIte, hi, Function.update_self, hr]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl,rfl,?_,ho.writeAndMove_readBack_idle⟩)
  funext j
  by_cases hj : j = q
  · subst j
    simp only [↓reduceIte, Function.update_self]
    rw [writeAndMove_readBack _ (by rw [hr]; decide)]
    apply Tape.ext
    · rfl
    · rfl
  · simp only [hj, ↓reduceIte, Function.update_of_ne hj]
    exact (hw j).writeAndMove_readBack_idle

theorem header_back_step {k : Nat} (q : Fin k) (inp : Tape)
    (work : Fin k → Tape) (out : Tape) (v h : Nat)
    (hp : Parked inp) (hw : ∀ j, Parked (work j)) (ho : Parked out) :
    (headerRegTM q).step
      {state := .back, input := inp,
       work := Function.update work q ⟨h,regCells v⟩, output := out} = some
      {state := if h = 0 then .done else .back, input := inp,
       work := Function.update work q ⟨if h = 0 then 1 else h-1,regCells v⟩, output := out} := by
  have hs : (⟨h,regCells v⟩ : Tape).read = Γ.start ↔ h = 0 := by
    constructor
    · intro hh
      by_contra hn
      exact regCells_ne_start (v := v) (j := h) (by omega) hh
    · rintro rfl; rfl
  simp only [TM.step, headerRegTM, reduceCtorEq, ↓reduceIte, Function.update_self, hs]
  refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl,hp.move_idle,?_,ho.writeAndMove_readBack_idle⟩)
  funext j
  by_cases hj : j = q
  · subst j
    simp only [↓reduceIte, Function.update_self]
    by_cases hh : h = 0
    · subst h
      simp [Tape.writeAndMove, Tape.write, Tape.move]
    · rw [writeAndMove_readBack _ (by intro he; exact hh (hs.mp he))]
      simp only [hh, ↓reduceIte]
      rfl
  · simp only [hj, ↓reduceIte, Function.update_of_ne hj]
    exact (hw j).writeAndMove_readBack_idle

theorem header_back_run {k : Nat} (q : Fin k) (inp : Tape)
    (work : Fin k → Tape) (out : Tape) (v h : Nat)
    (hp : Parked inp) (hw : ∀ j, Parked (work j)) (ho : Parked out) :
    (headerRegTM q).reachesIn (h+1)
      {state := .back, input := inp,
       work := Function.update work q ⟨h,regCells v⟩, output := out}
      {state := .done, input := inp,
       work := Function.update work q (regTape v), output := out} := by
  induction h with
  | zero =>
      exact .step (by simpa [regTape] using header_back_step q inp work out v 0 hp hw ho) .zero
  | succ h ih =>
      exact .step (by simpa using header_back_step q inp work out v (h+1) hp hw ho) ih

end IrrRAFEnumeration.SATSource

module

public import proofs.UnconstrainedPACDetection.FormulaLookupScan

@[expose] public section

namespace UnconstrainedPACDetection.FormulaLookupScan
open Complexity Complexity.TM

structure Action where
  next : Option (Option Bool)
  skip : Bool
  count : Bool
  output : Option Bool

def action (q : Option Bool) (b zero : Bool) : Action :=
  match event q b with
  | .pending a => ⟨some (some a),false,false,none⟩
  | .data a => ⟨some none,false,false,if zero then some a else none⟩
  | .literal => ⟨if zero then none else some none,!zero,false,none⟩
  | .clause => ⟨some none,false,true,none⟩

def put (t : Tape) : Option Bool → Tape
  | none => t
  | some b => t.writeAndMove (Γ.ofBool b) .right

def outWrite (o : Γ) : Option Bool → Γw
  | none => readBackWrite o
  | some b => if b then .one else .zero

def outDir (o : Γ) : Option Bool → Dir3
  | none => idleDir o
  | some _ => .right

/-- Query tape 0 is traversed without erasure; tape 1 accumulates clause marks.
The output receives the selected raw literal, hence remains empty for a missing occurrence. -/
def machine : TM 2 where
  Q := Option (Option Bool)
  qstart := some none
  qhalt := none
  δ := fun q i w o =>
    match q with
    | none => allIdle none i w o
    | some s =>
      if i = .start then
        (some s,fun j => readBackWrite (w j),readBackWrite o,
          .right,fun j => idleDir (w j),idleDir o)
      else if i = .blank then
        (none,fun j => readBackWrite (w j),readBackWrite o,
          idleDir i,fun j => idleDir (w j),idleDir o)
      else
        let a := action s (decide (i = .one)) (decide (w 0 = .blank))
        (a.next,fun j => if j = 0 then readBackWrite (w j)
          else if a.count then .one else readBackWrite (w j),outWrite o a.output,
          .right,fun j => if j = 0 then if a.skip then .right else idleDir (w j)
            else if a.count then .right else idleDir (w j),outDir o a.output)
  δ_right_of_start := by
    intro q i w o
    cases q with
    | none => exact rightOfStart_allIdle i w o
    | some s =>
      dsimp only
      split
      · exact ⟨fun _ => rfl,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
      · split
        · exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
        · refine ⟨fun _ => rfl,?_,?_⟩
          · intro j hj
            simp [hj,idleDir]
          · intro h
            cases (action s (decide (i = .one)) (decide (w 0 = .blank))).output <;>
              simp [outDir,h,idleDir]

def after (c : Cfg 2 machine.Q) (a : Action) : Cfg 2 machine.Q :=
  ⟨a.next,c.input.move .right,
    fun j => if j = 0 then if a.skip then (c.work j).move .right else c.work j
      else FormulaTokenCount.emit (c.work j) a.count,
    put c.output a.output⟩

theorem readBack_move (t : Tape) (d : Dir3) (h : t.read ≠ .start) :
    t.writeAndMove (readBackWrite t.read).toΓ d = t.move d := by
  have he : t.write (readBackWrite t.read).toΓ = t := by
    simpa [transitionTape,idleDir,h,Tape.move] using transitionTape_eq_self h
  exact congrArg (fun t : Tape => t.move d) he

theorem put_transition (t : Tape) (p : Option Bool) (h : t.read ≠ .start) :
    t.writeAndMove (outWrite t.read p).toΓ (outDir t.read p) = put t p := by
  cases p with
  | none => exact transitionTape_eq_self h
  | some b => cases b <;> rfl

theorem bit_step (s : Option Bool) (b z : Bool) (c : Cfg 2 machine.Q)
    (hs : c.state = some s) (hi : c.input.read = Γ.ofBool b)
    (hz : decide ((c.work 0).read = .blank) = z)
    (hw : ∀ j, (c.work j).read ≠ .start) (ho : c.output.read ≠ .start) :
    machine.step c = some (after c (action s b z)) := by
  have hd : decide (Γ.ofBool b = .one) = b := by cases b <;> rfl
  have hn : Γ.ofBool b ≠ .start := by cases b <;> decide
  have hb : Γ.ofBool b ≠ .blank := by cases b <;> decide
  simp only [TM.step,machine,hs,reduceCtorEq,↓reduceIte,hi,ite_eq_right hn,ite_eq_right hb,hd,hz]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    dsimp only [after]
    by_cases hj : j = 0
    · simp only [ite_eq_left hj]
      cases he : (action s b z).skip
      · simpa [he,transitionTape] using transitionTape_eq_self (hw j)
      · simpa [he] using readBack_move (c.work j) .right (hw j)
    · simp only [ite_eq_right hj]
      cases he : (action s b z).count
      · simpa [he,FormulaTokenCount.emit,transitionTape] using transitionTape_eq_self (hw j)
      · rfl
  · exact put_transition c.output _ ho

theorem put_prefix (t : Tape) (xs : List Bool) (p : Option Bool)
    (h : t.HasBinaryPrefix xs) :
    (put t p).HasBinaryPrefix (xs ++ p.toList) := by
  cases p with
  | none => simpa [put] using h
  | some b => simpa [put] using Tape.hasBinaryPrefix_write_bit b h

end UnconstrainedPACDetection.FormulaLookupScan

module

public import proofs.UnconstrainedPACDetection.VerifierBinaryProduct

@[expose] public section

/-! Uniform multiplication candidate. The transition table has fixed finite
control and three work tapes: multiplier, accumulator, shifted temporary.
The universal multiplication/runtime boundary remains to be proved. -/
namespace UnconstrainedPACDetection.VerifierProductMachine
open Complexity
open Complexity.TM

-- 0 seek multiplier end, 1 loop, 2 copy shifted accumulator, 3 erase old
-- accumulator, 4 rewind temporary, 5 add, 6 rewind input, 7 erase temporary,
-- 8 rewind accumulator, 9 halt. Flags store multiplier bit and carry.
abbrev State := Fin 10 × Bool × Bool

structure Action where
  next : State
  writes : Fin 3 → Γw
  inputDir : Dir3
  workDirs : Fin 3 → Dir3

def control (q : State) (i : Γ) (w : Fin 3 → Γ) : Action := Id.run do
  let mut a : Action := ⟨q, fun j => readBackWrite (w j), .stay, fun _ => .stay⟩
  match q.1.val with
  | 0 =>
    if w 0 = .blank then
      a := { a with next := (1, false, false), workDirs := ![.left, .stay, .stay] }
    else a := { a with workDirs := ![.right, .stay, .stay] }
  | 1 =>
    if w 0 = .start then
      a := { a with next := (9, false, false), workDirs := ![.right, .stay, .stay] }
    else a := { a with next := (2, VerifierBinaryAdd.bit (w 0), false), writes := ![readBackWrite (w 0), readBackWrite (w 1), .zero], workDirs := ![.stay, .stay, .right] }
  | 2 =>
    if w 1 = .blank then
      a := { a with next := (3, q.2.1, false), workDirs := ![.stay, .left, .stay] }
    else a := { a with writes := ![readBackWrite (w 0), readBackWrite (w 1), readBackWrite (w 1)], workDirs := ![.stay, .right, .right] }
  | 3 =>
    if w 1 = .start then
      a := { a with next := (4, q.2.1, false), workDirs := ![.stay, .right, .stay] }
    else a := { a with writes := ![readBackWrite (w 0), .blank, readBackWrite (w 2)], workDirs := ![.stay, .left, .stay] }
  | 4 =>
    if w 2 = .start then
      a := { a with next := (5, q.2.1, false), workDirs := ![.stay, .stay, .right] }
    else a := { a with workDirs := ![.stay, .stay, .left] }
  | 5 =>
    if (q.2.1 = false ∨ i = .blank) ∧ w 2 = .blank then
      a := { a with next := (6, false, false), writes := ![readBackWrite (w 0), if q.2.2 then .one else readBackWrite (w 1), readBackWrite (w 2)], workDirs := ![.stay, if q.2.2 then .right else .stay, .stay] }
    else
      let x := q.2.1 && VerifierBinaryAdd.bit i
      let y := VerifierBinaryAdd.bit (w 2)
      a := { a with next := (5, q.2.1, VerifierBinaryAdd.carry x y q.2.2), writes := ![readBackWrite (w 0), Γw.ofBool (VerifierBinaryAdd.digit x y q.2.2), readBackWrite (w 2)], inputDir := if q.2.1 then VerifierBinaryAdd.advance i else .stay, workDirs := ![.stay, .right, VerifierBinaryAdd.advance (w 2)] }
  | 6 =>
    if i = .start then a := { a with next := (7, false, false), inputDir := .right }
    else a := { a with inputDir := .left }
  | 7 =>
    if w 2 = .start then
      a := { a with next := (8, false, false), workDirs := ![.stay, .stay, .right] }
    else a := { a with writes := ![readBackWrite (w 0), readBackWrite (w 1), .blank], workDirs := ![.stay, .stay, .left] }
  | 8 =>
    if w 1 = .start then
      a := { a with next := (1, false, false), workDirs := ![.left, .right, .stay] }
    else a := { a with workDirs := ![.stay, .left, .stay] }
  | _ => pure ()
  return a

def markerDir (g : Γ) (d : Dir3) : Dir3 := if g = .start then .right else d

def machine : TM 3 where
  Q := State
  qstart := (0, false, false)
  qhalt := (9, false, false)
  δ := fun q i w o =>
    let a := control q i w
    (a.next, a.writes, readBackWrite o, markerDir i a.inputDir,
      fun j => markerDir (w j) (a.workDirs j), idleDir o)
  δ_right_of_start := by
    intro q i w o
    exact ⟨fun h => by simp [markerDir, h], fun j h => by simp [markerDir, h], idleDir_right_of_start⟩

/-- The multiplication candidate never changes the caller's parked output. -/
theorem output_step {c d : Cfg 3 machine.Q} (ho : c.output.read ≠ .start)
    (h : machine.step c = some d) : d.output = c.output := by
  have hn := state_ne_qhalt_of_step h
  simp only [TM.step, hn, ↓reduceIte] at h
  cases h
  exact transitionTape_eq_self ho

theorem output_run {c d : Cfg 3 machine.Q} {t : ℕ}
    (ho : c.output.read ≠ .start) (h : machine.reachesIn t c d) : d.output = c.output := by
  induction h with
  | zero => rfl
  | step hs _ ih =>
    have hb := output_step ho hs
    exact (ih (by simpa only [hb] using ho)).trans hb

end UnconstrainedPACDetection.VerifierProductMachine

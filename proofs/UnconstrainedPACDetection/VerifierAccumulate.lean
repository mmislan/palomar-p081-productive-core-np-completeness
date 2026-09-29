module

public import proofs.UnconstrainedPACDetection.VerifierBinaryAdd

@[expose] public section

/-! In-place accumulation candidate. Its split invariant permits overwriting
the old total while preserving the unread suffix. Full execution remains open. -/
namespace UnconstrainedPACDetection.VerifierAccumulate
open Complexity
open Complexity.TM

def Split (t : Tape) (emitted rest : List Bool) : Prop :=
  t.head = emitted.length+1 ∧ t.HasBinaryContent (emitted ++ rest)

theorem split_write (t : Tape) (emitted rest : List Bool) (b : Bool)
    (h : Split t emitted rest) :
    Split (t.writeAndMove (Γ.ofBool b) .right) (emitted ++ [b]) rest.tail := by
  rcases h with ⟨hh, hc⟩
  constructor
  · simp [Tape.writeAndMove, Tape.move, Tape.write_head, hh]
  · cases rest with
    | nil =>
      have hp : t.HasBinaryPrefix emitted :=
        ⟨hh, by simpa only [Tape.HasBinaryContent, List.append_nil] using hc⟩
      have hnew := Tape.hasBinaryPrefix_write_bit b hp
      simpa only [List.tail_nil, List.append_nil, Tape.HasBinaryContent] using hnew.2
    | cons x xs =>
      have hnew := Tape.HasBinaryContent.write_set b hc hh
        (show emitted.length < (emitted ++ x :: xs).length by simp)
      have hmove := hnew.move Dir3.right
      simpa [Tape.writeAndMove, List.set_append_right, List.append_assoc] using hmove

theorem split_suffix (t : Tape) (emitted rest : List Bool) (h : Split t emitted rest) :
    t.HasBinarySuffix rest := by
  rcases h with ⟨hh, hc⟩
  refine ⟨by omega, ?_, ?_, hc.cells_ne_start⟩
  · intro i hi
    rw [hh]
    have hbits := hc.1 (emitted.length+i) (by simp only [List.length_append]; omega)
    simpa [List.getElem_append_right, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbits
  · rw [hh]
    simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hc.2 (emitted.length+rest.length) (by simp)

def markerDir (g : Γ) (d : Dir3) : Dir3 := if g = .start then .right else d

def machine : TM 1 where
  Q := Fin 4 × Bool
  qstart := (0,false)
  qhalt := (3,false)
  δ := fun q i w o =>
    let carry := q.2
    let a : (Fin 4 × Bool) × Γw × Dir3 × Dir3 :=
      if q.1 = 0 then
        if i = .blank ∧ w 0 = .blank then
          ((1,false), if carry then .one else readBackWrite (w 0), .stay, if carry then .right else .stay)
        else
          ((0, VerifierBinaryAdd.carry (VerifierBinaryAdd.bit i) (VerifierBinaryAdd.bit (w 0)) carry),
            Γw.ofBool (VerifierBinaryAdd.digit (VerifierBinaryAdd.bit i) (VerifierBinaryAdd.bit (w 0)) carry),
            VerifierBinaryAdd.advance i, .right)
      else if q.1 = 1 then
        ((if i = .start then 2 else 1,false), readBackWrite (w 0), if i = .start then .right else .left, .stay)
      else if q.1 = 2 then
        ((if w 0 = .start then 3 else 2,false), readBackWrite (w 0), .stay, if w 0 = .start then .right else .left)
      else (q, readBackWrite (w 0), .stay, .stay)
    (a.1, fun _ => a.2.1, readBackWrite o, markerDir i a.2.2.1,
      fun j => markerDir (w j) a.2.2.2, idleDir o)
  δ_right_of_start := by
    intro q i w o
    exact ⟨fun h => by simp [markerDir, h], fun j h => by simp [markerDir, h], idleDir_right_of_start⟩

theorem scan_step (xs ys emitted : List Bool) (carry : Bool) (c : Cfg 1 machine.Q)
    (hq : c.state = (0,carry)) (hx : c.input.HasBinarySuffix xs)
    (hy : Split (c.work 0) emitted ys) (hout : c.output.read ≠ .start)
    (hne : xs ≠ [] ∨ ys ≠ []) :
    ∃ d, machine.step c = some d ∧
      d.state = (0, VerifierBinaryAdd.carry (xs.headD false) (ys.headD false) carry) ∧
      d.input.HasBinarySuffix xs.tail ∧
      Split (d.work 0) (emitted ++ [VerifierBinaryAdd.digit (xs.headD false) (ys.headD false) carry]) ys.tail ∧
      d.input.head = c.input.head + (if c.input.read = .blank then 0 else 1) ∧
      d.input.cells = c.input.cells ∧ d.output = c.output := by
  have hys := split_suffix _ emitted ys hy
  have hnb : ¬(c.input.read = .blank ∧ (c.work 0).read = .blank) := by
    rcases hne with hxne | hyne
    · cases xs with
      | nil => contradiction
      | cons a xs => cases a <;> simp [hx.read_cons, Γ.ofBool]
    · cases ys with
      | nil => contradiction
      | cons b ys => cases b <;> simp [hys.read_cons, Γ.ofBool]
  let digit := VerifierBinaryAdd.digit (VerifierBinaryAdd.bit c.input.read)
    (VerifierBinaryAdd.bit (c.work 0).read) carry
  let d : Cfg 1 machine.Q :=
    { state := (0, VerifierBinaryAdd.carry (VerifierBinaryAdd.bit c.input.read)
        (VerifierBinaryAdd.bit (c.work 0).read) carry),
      input := c.input.move (VerifierBinaryAdd.advance c.input.read),
      work := fun j => (c.work j).writeAndMove (Γ.ofBool digit) .right,
      output := c.output }
  have hw : ∀ j, (c.work j).read ≠ .start := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    simpa only [hj] using hys.read_ne_start
  refine ⟨d, ?_, ?_, VerifierBinaryAdd.suffix_advance hx, ?_, ?_, Tape.move_cells _ _, rfl⟩
  · have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, hnb, markerDir, hx.read_ne_start, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      simp only [hw j, ↓reduceIte]
      change (c.work j).writeAndMove (Γw.ofBool digit).toΓ .right =
        (c.work j).writeAndMove (Γ.ofBool digit) .right
      cases digit <;> rfl
    · exact transitionTape_eq_self hout
  · simp only [d, VerifierBinaryAdd.suffix_bit hx, VerifierBinaryAdd.suffix_bit hys]
    rfl
  · have h := split_write (c.work 0) emitted ys digit hy
    simpa only [d, digit, VerifierBinaryAdd.suffix_bit hx, VerifierBinaryAdd.suffix_bit hys] using h
  · dsimp only [d]
    by_cases hb : c.input.read = .blank <;> simp [VerifierBinaryAdd.advance, hb, Tape.move]

end UnconstrainedPACDetection.VerifierAccumulate

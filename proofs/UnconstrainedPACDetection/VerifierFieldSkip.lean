module

public import proofs.UnconstrainedPACDetection.VerifierAccumulate

@[expose] public section

/-! A fixed field skipper. The unary index is a count of fields, never a
coefficient value. Incomplete framing halts before exhausting the counter. -/
namespace UnconstrainedPACDetection.VerifierFieldSkip
open Complexity
open Complexity.TM
open VerifierAccumulate (markerDir)

def action (q : Fin 4) (i w : Γ) : Fin 4 × Dir3 × Dir3 :=
  if q = 0 then (if w = .one then 1 else 3, .stay, .stay)
  else if q = 1 then
    if i = .zero then (0, .right, .right)
    else if i = .one then (2, .right, .stay) else (3, .stay, .stay)
  else if q = 2 then
    if i = .zero ∨ i = .one then (1, .right, .stay) else (3, .stay, .stay)
  else (3, .stay, .stay)

def machine : TM 1 where
  Q := Fin 4
  qstart := 0
  qhalt := 3
  δ := fun q i w o =>
    let a := action q i (w 0)
    (a.1, fun j => readBackWrite (w j), readBackWrite o,
      markerDir i a.2.1, fun j => markerDir (w j) a.2.2, idleDir o)
  δ_right_of_start := by
    intro q i w o
    exact ⟨fun h => by simp [markerDir, h], fun j h => by simp [markerDir, h], idleDir_right_of_start⟩

def moved (c : Cfg 1 (Fin 4)) (q : Fin 4) (di dw : Dir3) : Cfg 1 (Fin 4) :=
  ⟨q, c.input.move di, fun j => (c.work j).move dw, c.output⟩

theorem step_action (c : Cfg 1 (Fin 4)) (q : Fin 4) (di dw : Dir3)
    (hn : c.state ≠ 3) (hi : c.input.read ≠ .start)
    (hw : (c.work 0).read ≠ .start) (ho : c.output.read ≠ .start)
    (ha : action c.state c.input.read (c.work 0).read = (q, di, dw)) :
    machine.step c = some (moved c q di dw) := by
  have hw' : ∀ j, (c.work j).read ≠ .start := by intro j; fin_cases j; exact hw
  have keep := transitionTape_eq_self ho
  simp only [TM.step, machine, hn, ↓reduceIte, ha]
  simp only [markerDir, ite_eq_right hi, ite_eq_right (hw' _)]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    exact writeAndMove_readBack _ (hw' j) dw
  · exact keep

/-- Scan one complete field after entering the scan phase. The counter
advances exactly once, at the field terminator. -/
theorem field_run (field suffix count : List Bool) (c : Cfg 1 (Fin 4))
    (hq : c.state = 1)
    (hi : c.input.HasBinarySuffix (BinaryFields.encodeField field ++ suffix))
    (hw : (c.work 0).HasBinarySuffix (true :: count))
    (ho : c.output.read ≠ .start) :
    ∃ d, machine.reachesIn (2*field.length+1) c d ∧ d.state = (0 : Fin 4) ∧
      d.input.HasBinarySuffix suffix ∧ (d.work 0).HasBinarySuffix count ∧
      d.input.head = c.input.head + (2*field.length+1) ∧
      (d.work 0).head = (c.work 0).head+1 ∧
      d.input.cells = c.input.cells ∧ (d.work 0).cells = (c.work 0).cells ∧ d.output = c.output := by
  induction field generalizing c with
  | nil =>
    have hi' : c.input.HasBinarySuffix (false :: suffix) := hi
    have hs := step_action c 0 .right .right (by rw [hq]; decide)
      hi.read_ne_start hw.read_ne_start ho (by simp [action, hq, hi'.read_cons, Γ.ofBool])
    refine ⟨moved c 0 .right .right, .step hs .zero, rfl,
      hi'.move_right_cons, hw.move_right_cons, ?_, rfl, rfl, rfl, rfl⟩
    simp [moved, Tape.move]
  | cons b field ih =>
    have hi' : c.input.HasBinarySuffix (true :: b :: (BinaryFields.encodeField field ++ suffix)) := hi
    let c1 := moved c 2 .right .stay
    have hs1 := step_action c 2 .right .stay (by rw [hq]; decide)
      hi.read_ne_start hw.read_ne_start ho (by simp [action, hq, hi'.read_cons, Γ.ofBool])
    have h1 : c1.input.HasBinarySuffix (b :: (BinaryFields.encodeField field ++ suffix)) := hi'.move_right_cons
    have w1 : (c1.work 0).HasBinarySuffix (true :: count) := hw
    let c2 := moved c1 1 .right .stay
    have hs2 := step_action c1 1 .right .stay (by change (2 : Fin 4) ≠ 3; decide)
      h1.read_ne_start w1.read_ne_start ho (by
        change action 2 c1.input.read (c1.work 0).read = _
        cases b <;> simp [action, h1.read_cons, Γ.ofBool])
    obtain ⟨d, hd, hq', hi'', hw'', hh, wh, hc, wc, hout⟩ :=
      ih c2 rfl h1.move_right_cons w1 ho
    refine ⟨d, ?_, hq', hi'', hw'', ?_, wh, hc, wc, hout⟩
    · have h := TM.reachesIn.step hs1 (TM.reachesIn.step hs2 hd)
      convert h using 1
    · simp only [c2, c1, moved, Tape.move] at hh
      simp only [List.length_cons]
      omega

end UnconstrainedPACDetection.VerifierFieldSkip

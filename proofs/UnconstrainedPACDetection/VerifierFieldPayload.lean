module

public import proofs.UnconstrainedPACDetection.VerifierFieldParser

@[expose] public section

/-! Consume one actual PAC field, emitting its payload and retaining the
unread suffix. This is the tape-boundary contract needed to iterate decoding. -/
namespace UnconstrainedPACDetection.VerifierFieldPayload
open Complexity
open Complexity.TM

abbrev Phase := VerifierFieldMachine.Phase

def machine : TM 0 where
  Q := Phase
  qstart := .scan
  qhalt := .done
  δ := fun q i w o =>
    match q with
    | .scan =>
      if i = .start then
        (.scan, fun j => readBackWrite (w j), readBackWrite o,
          .right, fun j => idleDir (w j), idleDir o)
      else if i = .one then
        (.payload, fun j => readBackWrite (w j), readBackWrite o,
          .right, fun j => idleDir (w j), idleDir o)
      else
        (.done, fun j => readBackWrite (w j), readBackWrite o,
          .right, fun j => idleDir (w j), idleDir o)
    | .payload =>
      (.scan, fun j => readBackWrite (w j), readBackWrite i,
        .right, fun j => idleDir (w j), .right)
    | .done => allIdle .done i w o
  δ_right_of_start := by
    intro q i w o
    cases q
    · dsimp only
      split
      · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
      · split <;> exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
    · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    · exact rightOfStart_allIdle i w o

/-- All payloads and suffixes: consume precisely one field, append precisely
its payload, and park the input head at the remaining suffix. -/
theorem field_boundary (field suffix : List Bool) :
    ∀ (c : Cfg 0 machine.Q) (emitted : List Bool),
    c.state = VerifierFieldMachine.Phase.scan →
    c.input.HasBinarySuffix (BinaryFields.encodeField field ++ suffix) →
    c.output.HasBinaryPrefix emitted →
    ∃ d, machine.reachesIn (2 * field.length + 1) c d ∧ machine.halted d ∧
      d.input.HasBinarySuffix suffix ∧ d.output.HasBinaryPrefix (emitted ++ field) := by
  induction field with
  | nil =>
    intro c emitted hs hi ho
    have hi' : c.input.HasBinarySuffix (false :: suffix) := hi
    let d : Cfg 0 machine.Q :=
      { state := .done, input := c.input.move .right,
        work := (fun j => nomatch j), output := c.output }
    have keep : c.output.writeAndMove (readBackWrite c.output.read).toΓ
        (idleDir c.output.read) = c.output :=
      transitionTape_eq_self (by rw [ho.read_blank]; decide)
    have step : machine.step c = some d := by
      have hr := hi'.read_cons
      simp [TM.step, machine, hs, hr, d, Γ.ofBool]
      exact ⟨by funext j; exact Fin.elim0 j, keep⟩
    exact ⟨d, .step step .zero, rfl, hi'.move_right_cons, by simpa using ho⟩
  | cons b field ih =>
    intro c emitted hs hi ho
    have hi' : c.input.HasBinarySuffix
        (true :: b :: (BinaryFields.encodeField field ++ suffix)) := hi
    let c₁ : Cfg 0 machine.Q :=
      { state := .payload, input := c.input.move .right,
        work := (fun j => nomatch j), output := c.output }
    let c₂ : Cfg 0 machine.Q :=
      { state := .scan, input := c₁.input.move .right,
        work := (fun j => nomatch j),
        output := c.output.writeAndMove (Γ.ofBool b) .right }
    have keep : c.output.writeAndMove (readBackWrite c.output.read).toΓ
        (idleDir c.output.read) = c.output :=
      transitionTape_eq_self (by rw [ho.read_blank]; decide)
    have step₁ : machine.step c = some c₁ := by
      have hr := hi'.read_cons
      simp [TM.step, machine, hs, hr, c₁, Γ.ofBool]
      exact ⟨by funext j; exact Fin.elim0 j, keep⟩
    have input₁ : c₁.input.HasBinarySuffix
        (b :: (BinaryFields.encodeField field ++ suffix)) := hi'.move_right_cons
    have step₂ : machine.step c₁ = some c₂ := by
      have hr := input₁.read_cons
      cases b <;> simp [TM.step, machine, c₁, c₂, hr, Γ.ofBool, readBackWrite] <;>
        (funext j; exact Fin.elim0 j)
    obtain ⟨d, hd, hh, hin, hout⟩ := ih c₂ (emitted ++ [b]) rfl
      input₁.move_right_cons (Tape.hasBinaryPrefix_write_bit b ho)
    refine ⟨d, ?_, hh, hin, ?_⟩
    · convert TM.reachesIn.step step₁ (TM.reachesIn.step step₂ hd) using 1
    · simpa [List.append_assoc] using hout

end UnconstrainedPACDetection.VerifierFieldPayload

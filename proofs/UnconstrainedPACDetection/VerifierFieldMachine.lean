module

public import proofs.UnconstrainedPACDetection.BinaryFields
public import proofs.Complexitylib.Models.TuringMachine.Combinators
public import proofs.Complexitylib.Models.TuringMachine.Tape.Encoding
public import proofs.Complexitylib.Classes.P.Defs

@[expose] public section

/-! A concrete finite machine for the existing PAC field encoder. -/
namespace UnconstrainedPACDetection.VerifierFieldMachine
open Complexity
open Complexity.TM

inductive Phase where
  | scan | payload | done
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.scan, .payload, .done}
  complete := fun q => by cases q <;> simp

def machine : TM 0 where
  Q := Phase
  qstart := .scan
  qhalt := .done
  δ := fun q i w o =>
    match q with
    | .scan =>
      if i = .start then
        (.scan, fun j => readBackWrite (w j), readBackWrite o,
          .right, fun j => idleDir (w j), .right)
      else if i = .blank then
        (.done, fun j => readBackWrite (w j), .zero,
          idleDir i, fun j => idleDir (w j), .right)
      else
        (.payload, fun j => readBackWrite (w j), .one,
          idleDir i, fun j => idleDir (w j), .right)
    | .payload =>
      (.scan, fun j => readBackWrite (w j), readBackWrite i,
        .right, fun j => idleDir (w j), .right)
    | .done => allIdle .done i w o
  δ_right_of_start := by
    intro q i w o
    cases q
    · dsimp only
      split
      · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
      · split <;> exact ⟨fun h => by contradiction,
          fun _ => idleDir_right_of_start, fun _ => rfl⟩
    · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    · exact rightOfStart_allIdle i w o

/-- Simulation invariant: unread payload on input, emitted bits on output.
Each payload bit takes two transitions; the delimiter takes one. -/
theorem scan (xs : List Bool) : ∀ (c : Cfg 0 machine.Q) (emitted : List Bool),
    c.state = Phase.scan → c.input.HasBinarySuffix xs →
    c.output.HasBinaryPrefix emitted →
    ∃ d, machine.reachesIn (2 * xs.length + 1) c d ∧ machine.halted d ∧
      d.output.HasBinaryPrefix (emitted ++ BinaryFields.encodeField xs) := by
  induction xs with
  | nil =>
    intro c emitted hs hi ho
    let d : Cfg 0 machine.Q :=
      { state := .done, input := c.input, work := (fun j => nomatch j),
        output := c.output.writeAndMove Γ.zero .right }
    have step : machine.step c = some d := by
      have hr := hi.read_nil
      simp [TM.step, machine, hs, hr, d, idleDir, Tape.move]
      funext j; exact Fin.elim0 j
    refine ⟨d, .step step .zero, rfl, ?_⟩
    exact Tape.hasBinaryPrefix_write_bit false ho
  | cons b xs ih =>
    intro c emitted hs hi ho
    let c₁ : Cfg 0 machine.Q :=
      { state := .payload, input := c.input, work := (fun j => nomatch j),
        output := c.output.writeAndMove Γ.one .right }
    let c₂ : Cfg 0 machine.Q :=
      { state := .scan, input := c.input.move .right, work := (fun j => nomatch j),
        output := c₁.output.writeAndMove (Γ.ofBool b) .right }
    have step₁ : machine.step c = some c₁ := by
      have hr := hi.read_cons
      cases b <;> simp [TM.step, machine, hs, hr, Γ.ofBool, c₁, idleDir, Tape.move] <;> (funext j; exact Fin.elim0 j)
    have step₂ : machine.step c₁ = some c₂ := by
      have hr := hi.read_cons
      cases b <;> simp [TM.step, machine, c₁, c₂, hr, Γ.ofBool, readBackWrite] <;> (funext j; exact Fin.elim0 j)
    have out₁ : c₁.output.HasBinaryPrefix (emitted ++ [true]) :=
      Tape.hasBinaryPrefix_write_bit true ho
    have out₂ : c₂.output.HasBinaryPrefix ((emitted ++ [true]) ++ [b]) :=
      Tape.hasBinaryPrefix_write_bit b out₁
    obtain ⟨d, hd, hh, hout⟩ := ih c₂ _ rfl hi.move_right_cons out₂
    refine ⟨d, ?_, hh, ?_⟩
    · convert TM.reachesIn.step step₁ (TM.reachesIn.step step₂ hd) using 1
    · simpa [BinaryFields.encodeField, List.append_assoc] using hout

theorem computes : machine.ComputesInTime BinaryFields.encodeField (fun n => 2*n+2) := by
  intro xs
  let c : Cfg 0 machine.Q :=
    { state := .scan, input := (Tape.init (xs.map Γ.ofBool)).move .right,
      work := (fun j => nomatch j), output := (Tape.init []).move .right }
  have step : machine.step (machine.initCfg xs) = some c := by
    simp [TM.step, machine, c, Tape.read, Tape.init, readBackWrite,
      Tape.writeAndMove, Tape.write, Tape.move]
    funext j; exact Fin.elim0 j
  obtain ⟨d, hd, hh, ho⟩ := scan xs c [] rfl
    (Tape.init_move_right_hasBinarySuffix xs) Tape.init_nil_move_right_hasBinaryPrefix_nil
  refine ⟨d, 2*xs.length+2, le_rfl, ?_, hh, ?_⟩
  · convert TM.reachesIn.step step hd using 1
  · simpa using ho.hasOutput

theorem encodeField_mem_FP : BinaryFields.encodeField ∈ Complexity.FP := by
  refine ⟨1, 0, machine, (fun n => 2*n+2), computes, ?_⟩
  have hn : (fun n : ℕ => n) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa only [pow_one] using BigO.refl (fun n : ℕ => n)
  have htwo : (fun n : ℕ => 2*n) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa [two_mul] using BigO.add hn hn
  exact BigO.add htwo (BigO.const_le_pow 2 1)

end UnconstrainedPACDetection.VerifierFieldMachine




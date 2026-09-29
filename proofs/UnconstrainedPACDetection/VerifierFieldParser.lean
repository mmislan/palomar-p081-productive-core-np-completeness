module

public import proofs.UnconstrainedPACDetection.VerifierFieldMachine
public import proofs.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

@[expose] public section

/-! Linear-time syntax recognition for the actual PAC field decoder.
This checks framing only; it does not replace payload decoding or arithmetic. -/
namespace UnconstrainedPACDetection.VerifierFieldParser
open Complexity
open Complexity.TM

inductive Mode where
  | ready | opened | payload
  deriving DecidableEq

instance : Fintype Mode where
  elems := {.ready, .opened, .payload}
  complete := fun q => by cases q <;> simp

def next : Mode → Bool → Mode
  | .payload, _ => .opened
  | _, false => .ready
  | _, true => .payload

def run : Mode → List Bool → Bool
  | q, [] => decide (q = .ready)
  | q, b :: bs => run (next q b) bs

def nonemptyDecoded (xs : List Bool) : Bool :=
  match BinaryFields.decode xs with
  | some (_ :: _) => true
  | _ => false

theorem run_correct (xs : List Bool) :
    run .ready xs = (BinaryFields.decode xs).isSome ∧
    run .opened xs = nonemptyDecoded xs := by
  cases xs with
  | nil => simp [run, BinaryFields.decode, nonemptyDecoded]
  | cons b bs =>
    cases b with
    | false =>
      have h := (run_correct bs).1
      simp [run, next, BinaryFields.decode, nonemptyDecoded, h]
      cases BinaryFields.decode bs <;> rfl
    | true =>
      cases bs with
      | nil => simp [run, next, BinaryFields.decode, nonemptyDecoded]
      | cons b bs =>
        have h := (run_correct bs).2
        simp only [run, next, h]
        cases hd : BinaryFields.decode bs with
        | none => simp [BinaryFields.decode, nonemptyDecoded, hd]
        | some fs => cases fs <;> simp [BinaryFields.decode, nonemptyDecoded, hd]
termination_by xs.length

def machine : TM 0 where
  Q := Option Mode
  qstart := some .ready
  qhalt := none
  δ := fun q i w o =>
    match q with
    | none => allIdle none i w o
    | some m =>
      if i = .start then
        (some m, fun j => readBackWrite (w j), readBackWrite o,
          .right, fun j => idleDir (w j), idleDir o)
      else if i = .blank then
        (none, fun j => readBackWrite (w j),
          readBackWrite (Γ.ofBool (decide (m = .ready))),
          idleDir i, fun j => idleDir (w j), .right)
      else
        (some (next m (decide (i = .one))), fun j => readBackWrite (w j), readBackWrite o,
          .right, fun j => idleDir (w j), idleDir o)
  δ_right_of_start := by
    intro q i w o
    cases q with
    | none => exact rightOfStart_allIdle i w o
    | some m =>
      dsimp only
      split
      · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
      · split
        · exact ⟨fun h => by contradiction, fun _ => idleDir_right_of_start, fun _ => rfl⟩
        · exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩

theorem scan (xs : List Bool) : ∀ (m : Mode) (c : Cfg 0 machine.Q),
    c.state = some m → c.input.HasBinarySuffix xs →
    c.output.HasBinaryPrefix [] →
    ∃ d, machine.reachesIn (xs.length + 1) c d ∧ machine.halted d ∧
      d.output.HasBinaryPrefix [run m xs] := by
  induction xs with
  | nil =>
    intro m c hs hi ho
    let d : Cfg 0 machine.Q :=
      { state := none, input := c.input, work := (fun j => nomatch j),
        output := c.output.writeAndMove (Γ.ofBool (decide (m = .ready))) .right }
    have step : machine.step c = some d := by
      have hr := hi.read_nil
      cases m <;> simp [TM.step, machine, hs, hr, d, Γ.ofBool, readBackWrite, idleDir, Tape.move] <;>
        (funext j; exact Fin.elim0 j)
    exact ⟨d, .step step .zero, rfl, Tape.hasBinaryPrefix_write_bit _ ho⟩
  | cons b xs ih =>
    intro m c hs hi ho
    let c₁ : Cfg 0 machine.Q :=
      { state := some (next m b), input := c.input.move .right,
        work := (fun j => nomatch j), output := c.output }
    have keep : c.output.writeAndMove (readBackWrite c.output.read).toΓ
        (idleDir c.output.read) = c.output :=
      transitionTape_eq_self (by rw [ho.read_blank]; decide)
    have step : machine.step c = some c₁ := by
      have hr := hi.read_cons
      cases b <;> simp [TM.step, machine, hs, hr, c₁, Γ.ofBool] <;>
        exact ⟨by funext j; exact Fin.elim0 j, keep⟩
    obtain ⟨d, hd, hh, hout⟩ := ih (next m b) c₁ rfl hi.move_right_cons ho
    exact ⟨d, .step step hd, hh, hout⟩

theorem computes : machine.ComputesInTime
    (fun xs => [(BinaryFields.decode xs).isSome]) (fun n => n+2) := by
  intro xs
  let c : Cfg 0 machine.Q :=
    { state := some .ready, input := (Tape.init (xs.map Γ.ofBool)).move .right,
      work := (fun j => nomatch j), output := (Tape.init []).move .right }
  have step : machine.step (machine.initCfg xs) = some c := by
    simp [TM.step, machine, c, Tape.read, Tape.init, readBackWrite, idleDir,
      Tape.writeAndMove, Tape.write, Tape.move]
    funext j; exact Fin.elim0 j
  obtain ⟨d, hd, hh, ho⟩ := scan xs .ready c rfl
    (Tape.init_move_right_hasBinarySuffix xs) Tape.init_nil_move_right_hasBinaryPrefix_nil
  refine ⟨d, xs.length+2, le_rfl, .step step hd, hh, ?_⟩
  simpa only [(run_correct xs).1] using ho.hasOutput

theorem syntax_mem_FP : (fun xs => [(BinaryFields.decode xs).isSome]) ∈ Complexity.FP := by
  refine ⟨1, 0, machine, (fun n => n+2), computes, ?_⟩
  have hn : (fun n : ℕ => n) =O ((· ^ 1) : ℕ → ℕ) := by
    simpa only [pow_one] using BigO.refl (fun n : ℕ => n)
  exact BigO.add hn (BigO.const_le_pow 2 1)

end UnconstrainedPACDetection.VerifierFieldParser

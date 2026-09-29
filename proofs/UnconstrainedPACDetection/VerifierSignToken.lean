module

public import proofs.UnconstrainedPACDetection.VerifierIndexedField
public import proofs.UnconstrainedPACDetection.VerifierAccumulate

@[expose] public section

/-! Read the first doubled token of a signed field, leaving its magnitude
framing in place for the existing field parser. -/
namespace UnconstrainedPACDetection.VerifierSignToken
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierAccumulate (markerDir)

def machine : TM 1 where
  Q := Fin 3
  qstart := 0
  qhalt := 2
  δ := fun q i w o =>
    (if q = 0 then 1 else 2,
      fun j => if q = 1 then (if i = .one then .one else .zero) else readBackWrite (w j),
      readBackWrite o, markerDir i .right, fun j => markerDir (w j) .stay, idleDir o)
  δ_right_of_start := by
    intro q i w o
    exact ⟨fun h => by simp [markerDir, h], fun j h => by simp [markerDir, h], idleDir_right_of_start⟩

/-- Exactly two transitions consume true,sign. The sign is saved at head1
on work0, and the following magnitude field has not yet been consumed. -/
theorem sign_hoare (sign : Bool) (rest : List Bool) (out₀ : Tape)
    (ho : out₀.read ≠ .start) :
    machine.HoareTime
      (fun inp work out => inp.HasBinarySuffix (true :: sign :: rest) ∧ work 0 = wordTape [] ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix rest ∧ work 0 = wordTape [sign] ∧ out = out₀) 2 := by
  rintro inp work out ⟨hi, hw, rfl⟩
  have hwork : work = fun _ => wordTape [] := by funext j; fin_cases j; exact hw
  subst work
  let c1 : Cfg 1 (Fin 3) := ⟨1, inp.move .right, fun _ => wordTape [], out⟩
  let c2 : Cfg 1 (Fin 3) :=
    ⟨2, (inp.move .right).move .right, fun _ => (wordTape []).write (Γ.ofBool sign), out⟩
  have keep := transitionTape_eq_self ho
  have keepO : out.writeAndMove (readBackWrite out.read) (idleDir out.read) = out := keep
  have blank : (wordTape []).read = .blank := rfl
  have keepW : (wordTape []).writeAndMove (readBackWrite Γ.blank) .stay = wordTape [] := by
    exact writeAndMove_readBack _ (by rw [blank]; decide) .stay
  have h1 : machine.step ⟨machine.qstart, inp, fun _ => wordTape [], out⟩ = some c1 := by
    simp [TM.step, machine, c1, markerDir, blank]
    exact ⟨funext (fun _ => keepW), keepO⟩
  have htail := hi.move_right_cons
  have h2 : machine.step c1 = some c2 := by
    cases sign <;>
      simp [TM.step, machine, c1, c2, htail.read_cons, Γ.ofBool, markerDir, blank] <;>
      exact ⟨rfl, keepO⟩
  have hp := Tape.hasBinaryPrefix_write_bit sign Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hs : ((wordTape []).write (Γ.ofBool sign)).HasBinaryString [sign] :=
    Tape.hasBinaryString_of_hasBinaryPrefix hp rfl rfl
  have hz : ((wordTape []).write (Γ.ofBool sign)).cells 0 = .start := by
    simp [wordTape, Tape.write, Tape.move, Tape.init]
  exact ⟨c2, 2, le_rfl, .step h1 (.step h2 .zero), rfl, htail.move_right_cons,
    Tape.eq_init_move_right_of_hasBinaryString hs hz, rfl⟩

end UnconstrainedPACDetection.VerifierSignToken

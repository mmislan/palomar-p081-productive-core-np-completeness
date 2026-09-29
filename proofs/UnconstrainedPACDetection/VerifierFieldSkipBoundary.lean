module

public import proofs.UnconstrainedPACDetection.VerifierFieldSkip

@[expose] public section

/-! Indexed field access advances by a unary number of complete framed fields. -/
namespace UnconstrainedPACDetection.VerifierFieldSkip
open Complexity
open Complexity.TM

theorem prefix_run (fields : List (List Bool)) (suffix rest : List Bool)
    (c : Cfg 1 (Fin 4)) (hq : c.state = 0)
    (hi : c.input.HasBinarySuffix (BinaryFields.encode fields ++ suffix))
    (hw : (c.work 0).HasBinarySuffix (List.replicate fields.length true ++ rest))
    (ho : c.output.read ≠ .start) :
    ∃ d, machine.reachesIn ((BinaryFields.encode fields).length+fields.length) c d ∧
      d.state = (0 : Fin 4) ∧ d.input.HasBinarySuffix suffix ∧
      (d.work 0).HasBinarySuffix rest ∧
      d.input.head = c.input.head + (BinaryFields.encode fields).length ∧
      (d.work 0).head = (c.work 0).head+fields.length ∧
      d.input.cells = c.input.cells ∧ (d.work 0).cells = (c.work 0).cells ∧ d.output = c.output := by
  induction fields generalizing c with
  | nil =>
    exact ⟨c, .zero, hq, hi, hw, by simp [BinaryFields.encode], by simp, rfl, rfl, rfl⟩
  | cons field fields ih =>
    have hw' : (c.work 0).HasBinarySuffix (true :: (List.replicate fields.length true ++ rest)) := by
      simpa only [List.length_cons, List.replicate_succ, List.cons_append] using hw
    let c1 := moved c 1 .stay .stay
    have hs := step_action c 1 .stay .stay (by rw [hq]; decide)
      hi.read_ne_start hw.read_ne_start ho (by simp [action, hq, hw'.read_cons, Γ.ofBool])
    have hi' : c1.input.HasBinarySuffix
        (BinaryFields.encodeField field ++ (BinaryFields.encode fields ++ suffix)) := by
      simpa [c1, moved, Tape.move, BinaryFields.encode, List.append_assoc] using hi
    obtain ⟨d, hd, hq', hi'', hw'', hh, wh, hc, wc, hout⟩ :=
      field_run field (BinaryFields.encode fields ++ suffix)
        (List.replicate fields.length true ++ rest) c1 rfl hi' hw' ho
    obtain ⟨e, he, eq, ei, ew, eh, ewh, ec, ewc, eo⟩ :=
      ih d hq' hi'' hw'' (by rw [hout]; simpa [c1, moved] using ho)
    refine ⟨e, ?_, eq, ei, ew, ?_, ?_, ec.trans hc, ewc.trans wc, eo.trans hout⟩
    · have h := machine.reachesIn_trans (TM.reachesIn.step hs hd) he
      have htime :
          (2 * field.length + 1 + 1) +
              ((BinaryFields.encode fields).length + fields.length) =
            (BinaryFields.encode (field :: fields)).length + (field :: fields).length := by
        simp [BinaryFields.encode, List.length_flatMap, BinaryFields.encodeField_length]
        omega
      exact htime ▸ h
    · simp only [c1, moved, Tape.move] at hh
      simp only [BinaryFields.encode, List.flatMap_cons, List.length_append,
        BinaryFields.encodeField_length] at eh ⊢
      omega
    · simp only [c1, moved, Tape.move] at wh
      simp only [List.length_cons]
      omega

/-- Starting with a unary index k, halt at the suffix after k complete fields.
Both tapes retain every cell, and the exhausted counter is explicit. -/
theorem skip_run (fields : List (List Bool)) (suffix : List Bool)
    (c : Cfg 1 (Fin 4)) (hq : c.state = 0)
    (hi : c.input.HasBinarySuffix (BinaryFields.encode fields ++ suffix))
    (hw : (c.work 0).HasBinarySuffix (List.replicate fields.length true))
    (ho : c.output.read ≠ .start) :
    ∃ d, machine.reachesIn ((BinaryFields.encode fields).length+fields.length+1) c d ∧
      machine.halted d ∧ d.input.HasBinarySuffix suffix ∧
      (d.work 0).HasBinarySuffix [] ∧
      d.input.head = c.input.head + (BinaryFields.encode fields).length ∧
      (d.work 0).head = (c.work 0).head+fields.length ∧
      d.input.cells = c.input.cells ∧ (d.work 0).cells = (c.work 0).cells ∧ d.output = c.output := by
  obtain ⟨d, hd, hq', hi', hw', hh, wh, hc, wc, hout⟩ :=
    prefix_run fields suffix [] c hq hi (by simpa using hw) ho
  have hs := step_action d 3 .stay .stay (by rw [hq']; decide)
    hi'.read_ne_start hw'.read_ne_start (by simpa only [hout] using ho)
    (by simp [action, hq', hw'.read_nil])
  refine ⟨moved d 3 .stay .stay, ?_, rfl, hi', hw', hh, wh, hc, wc, hout⟩
  exact machine.reachesIn_trans hd (.step hs .zero)

end UnconstrainedPACDetection.VerifierFieldSkip

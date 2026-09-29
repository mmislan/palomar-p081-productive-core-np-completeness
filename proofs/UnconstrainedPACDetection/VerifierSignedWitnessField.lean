module

public import proofs.UnconstrainedPACDetection.VerifierSignedField
public import proofs.Complexitylib.Models.TuringMachine.Internal

@[expose] public section

/-! Signed flow extraction from a saved witness, preserving the coefficient. -/
namespace UnconstrainedPACDetection.VerifierSignedWitnessField
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)

abbrev sourceMachine := VerifierSignedField.machine
def buffered : TM 4 := retargetInput sourceMachine
def machine : TM 5 := placeWorkTM 1 0 buffered

theorem retarget_run {t : ℕ} {c d : Cfg 3 sourceMachine.Q}
    (h : sourceMachine.reachesIn t c d) (hi : c.input.StartInvariant)
    (realInput : Tape) (hr : realInput.read ≠ .start) :
    buffered.reachesIn t (retargetWrap sourceMachine realInput c)
      (retargetWrap sourceMachine realInput d) := by
  have hidle : realInput.move (idleDir realInput.read) = realInput := by
    simp [idleDir, hr, Tape.move]
  induction h with
  | zero => exact .zero
  | step hs _ ih =>
    have hc := input_cells_eq_of_step hs
    have hi' : _ := And.intro (hc ▸ hi.1) (fun j hj => hc ▸ hi.2 j hj)
    have step := retargetInput_step_commute sourceMachine hs realInput hi
    rw [hidle] at step
    exact .step step (ih hi')

/-- Coefficient0/index1/magnitude2/sign3/witness4. All source cells and the
real source cursor are preserved; selected sign/magnitude are separate words. -/
theorem extraction_run (fields : List (List Bool)) (sign : Bool) (mag suffix : List Bool)
    (c : Cfg 5 machine.Q) (hq : c.state = machine.qstart)
    (hc : (c.work 0).read ≠ .start)
    (hk : c.work 1 = VerifierIndexedField.counter fields.length)
    (he : c.work 2 = wordTape []) (hs : c.work 3 = wordTape [])
    (hi : (c.work 4).HasBinarySuffix
      (BinaryFields.encode fields ++ (BinaryFields.encodeField (sign :: mag) ++ suffix)))
    (hm : (c.work 4).StartInvariant)
    (hr : c.input.read ≠ .start) (ho : c.output.read ≠ .start) (hoHead : 1 ≤ c.output.head) :
    ∃ t d, t ≤ (BinaryFields.encode fields).length+fields.length+3*mag.length+10 ∧
      machine.reachesIn t c d ∧ machine.halted d ∧
      d.work 0 = c.work 0 ∧ d.work 1 = VerifierIndexedField.exhausted fields.length ∧
      d.work 2 = wordTape mag ∧ d.work 3 = wordTape [sign] ∧
      (d.work 4).HasBinarySuffix suffix ∧ (d.work 4).cells = (c.work 4).cells ∧
      d.input = c.input ∧ d.output = c.output := by
  let s : Cfg 3 sourceMachine.Q :=
    ⟨sourceMachine.qstart, c.work 4, VerifierSignedField.before fields.length, c.output⟩
  let embed := fun z : Cfg 3 sourceMachine.Q =>
    placeWorkCfg buffered 1 0 c.work (retargetWrap sourceMachine c.input z)
  have hembed : embed s = c := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · funext j
      fin_cases j <;> simp [embed, s, placeWorkCfg, placeWorkInMiddle, placeWorkCoord,
        retargetWrap, VerifierSignedField.before, hk, he, hs]
    · rfl
  obtain ⟨d, t, hb, hd, hh, hid, hwd, hod⟩ :=
    VerifierSignedField.signed_field_hoare fields sign mag suffix c.output ho hoHead
      (c.work 4) (VerifierSignedField.before fields.length) c.output ⟨hi, rfl, rfl⟩
  have hret := retarget_run hd hm c.input hr
  have hplaced := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    buffered 1 0 c.work hret (by
      intro j hj
      have hj0 : j = 0 := by
        apply Fin.ext
        change j.val = 0
        simp only [placeWorkInMiddle] at hj
        omega
      subst j
      exact hc)
  have hic := input_cells_eq_of_reachesIn hd
  refine ⟨t, embed d, hb, ?_, hh, ?_, ?_, ?_, ?_, ?_, ?_, rfl, hod⟩
  · change machine.reachesIn t (embed s) (embed d) at hplaced
    simpa only [hembed] using hplaced
  · simp [embed, placeWorkCfg, placeWorkInMiddle]
  · simpa [embed, placeWorkCfg, placeWorkInMiddle, placeWorkCoord, retargetWrap,
      VerifierSignedField.after] using congrFun hwd 0
  · simpa [embed, placeWorkCfg, placeWorkInMiddle, placeWorkCoord, retargetWrap,
      VerifierSignedField.after] using congrFun hwd 1
  · simpa [embed, placeWorkCfg, placeWorkInMiddle, placeWorkCoord, retargetWrap,
      VerifierSignedField.after] using congrFun hwd 2
  · simpa [embed, placeWorkCfg, placeWorkInMiddle, placeWorkCoord, retargetWrap] using hid
  · simpa [embed, placeWorkCfg, placeWorkInMiddle, placeWorkCoord, retargetWrap] using hic

end UnconstrainedPACDetection.VerifierSignedWitnessField

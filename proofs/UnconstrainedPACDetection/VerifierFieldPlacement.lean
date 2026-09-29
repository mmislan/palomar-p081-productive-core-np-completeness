module

public import proofs.UnconstrainedPACDetection.VerifierFieldBuffer
public import proofs.UnconstrainedPACDetection.VerifierBufferedProduct
public import proofs.Complexitylib.Models.TuringMachine.Placement.Internal

@[expose] public section

/-! Place the actual field parser in the operand slots required by multiplication. -/
namespace UnconstrainedPACDetection.VerifierFieldPlacement
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)

def machine (pre post : ℕ) : TM (pre+1+post) :=
  placeWorkTM pre post VerifierFieldBuffer.preparedMachine

def slot (pre post : ℕ) : Fin (pre+1+post) := placeWorkIdx pre post (0 : Fin 1)

theorem middle_iff (pre post : ℕ) (j : Fin (pre+1+post)) :
    placeWorkInMiddle pre 1 j ↔ j = slot pre post := by
  constructor
  · intro h
    apply Fin.ext
    simp only [placeWorkInMiddle] at h
    change j.val = pre + 0
    omega
  · rintro rfl
    exact placeWorkInMiddle_placeWorkIdx pre post (0 : Fin 1)

/-- One parsed field replaces exactly its selected empty tape. Every other
physical work tape is a preserved frame, including previously parsed operands. -/
theorem field_hoare (pre post : ℕ) (field suffix : List Bool)
    (frame : Fin (pre+1+post) → Tape) (out₀ : Tape)
    (hempty : frame (slot pre post) = wordTape [])
    (hframe : ∀ j, j ≠ slot pre post → (frame j).read ≠ .start)
    (hout : out₀.read ≠ .start) (houtHead : 1 ≤ out₀.head) :
    (machine pre post).HoareTime
      (fun inp work out => inp.HasBinarySuffix (BinaryFields.encodeField field ++ suffix) ∧
        work = frame ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix suffix ∧
        work = Function.update frame (slot pre post) (wordTape field) ∧ out = out₀)
      (3*field.length+5) := by
  rintro inp work out ⟨hin, rfl, rfl⟩
  let s : Cfg 1 VerifierFieldBuffer.preparedMachine.Q :=
    ⟨VerifierFieldBuffer.preparedMachine.qstart, inp, fun _ => work (slot pre post), out⟩
  have hp : (work (slot pre post)).HasBinaryPrefix [] := by
    rw [hempty]; exact Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hz : (work (slot pre post)).cells 0 = .start := by rw [hempty]; rfl
  obtain ⟨d, t, hb, hd, hh, hi, hs, hzero, ho⟩ :=
    VerifierFieldBuffer.prepared_hoare field suffix out hout houtHead inp
      (fun _ => work (slot pre post)) out ⟨hin, hp, hz, rfl⟩
  have he : placeWorkCfg VerifierFieldBuffer.preparedMachine pre post work s =
      (⟨(machine pre post).qstart, inp, work, out⟩ : Cfg (pre+1+post) (machine pre post).Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      by_cases hj : j = slot pre post
      · subst j
        exact placeWorkCfg_work_middle _ pre post work s 0
      · exact placeWorkCfg_work_extra _ pre post work s j ((middle_iff pre post j).not.mpr hj)
    · rfl
  have hplaced := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierFieldBuffer.preparedMachine pre post work hd (by
      intro j hj
      apply hframe j
      exact ((middle_iff pre post j).not).mp hj)
  have hdword : d.work 0 = wordTape field := Tape.eq_init_move_right_of_hasBinaryString hs hzero
  refine ⟨placeWorkCfg VerifierFieldBuffer.preparedMachine pre post work d, t, hb,
    ?_, hh, hi, ?_, ho⟩
  · change (placeWorkTM pre post VerifierFieldBuffer.preparedMachine).reachesIn t _ _
    change (placeWorkTM pre post VerifierFieldBuffer.preparedMachine).reachesIn t
      (placeWorkCfg VerifierFieldBuffer.preparedMachine pre post work s)
      (placeWorkCfg VerifierFieldBuffer.preparedMachine pre post work d) at hplaced
    simpa only [he] using hplaced
  · funext j
    by_cases hj : j = slot pre post
    · subst j
      rw [Function.update_self]
      exact (placeWorkCfg_work_middle _ pre post work d 0).trans hdword
    · rw [Function.update_of_ne hj]
      exact placeWorkCfg_work_extra _ pre post work d j ((middle_iff pre post j).not.mpr hj)

end UnconstrainedPACDetection.VerifierFieldPlacement

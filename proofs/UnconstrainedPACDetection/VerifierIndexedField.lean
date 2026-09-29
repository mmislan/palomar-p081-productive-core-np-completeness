module

public import proofs.UnconstrainedPACDetection.VerifierFieldSkipBoundary
public import proofs.UnconstrainedPACDetection.VerifierFieldPlacement

@[expose] public section

/-! Actual indexed payload extraction with a prepared unary field index. -/
namespace UnconstrainedPACDetection.VerifierIndexedField
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)

def counter (k : ℕ) := wordTape (List.replicate k true)
def exhausted (k : ℕ) : Tape := ⟨k+1, (counter k).cells⟩
def before (k : ℕ) : Fin 2 → Tape := ![counter k, wordTape []]
def middle (k : ℕ) : Fin 2 → Tape := ![exhausted k, wordTape []]
def after (k : ℕ) (field : List Bool) : Fin 2 → Tape := ![exhausted k, wordTape field]
def skip : TM 2 := placeWorkTM 0 1 VerifierFieldSkip.machine
def machine : TM 2 := seqTM skip (VerifierFieldPlacement.machine 1 0)

theorem exhausted_off (k : ℕ) : (exhausted k).read ≠ .start := by
  have h : (exhausted k).HasBinaryPrefix (List.replicate k true) :=
    ⟨by simp [exhausted], (Tape.init_move_right_hasBinaryString (List.replicate k true)).2⟩
  rw [h.read_blank]
  decide

theorem skip_hoare (skipped : List (List Bool)) (suffix : List Bool) (out₀ : Tape)
    (ho : out₀.read ≠ .start) :
    skip.HoareTime
      (fun inp work out => inp.HasBinarySuffix (BinaryFields.encode skipped ++ suffix) ∧
        work = before skipped.length ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix suffix ∧ work = middle skipped.length ∧ out = out₀)
      ((BinaryFields.encode skipped).length+skipped.length+1) := by
  rintro inp work out ⟨hi, rfl, rfl⟩
  let c : Cfg 1 (Fin 4) := ⟨0, inp, fun _ => counter skipped.length, out⟩
  obtain ⟨d, hd, hh, hin, hw, ih, wh, ic, wc, hout⟩ :=
    VerifierFieldSkip.skip_run skipped suffix c rfl hi
      (Tape.init_move_right_hasBinaryString _).hasBinarySuffix ho
  have he : placeWorkCfg VerifierFieldSkip.machine 0 1 (before skipped.length) c =
      (⟨skip.qstart, inp, before skipped.length, out⟩ : Cfg 2 skip.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [placeWorkCfg, placeWorkInMiddle, c, before]
    · rfl
  have hplaced := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierFieldSkip.machine 0 1 (before skipped.length) hd (by
      intro j hj
      have hj1 : j = 1 := by
        apply Fin.ext
        change j.val = 1
        simp only [placeWorkInMiddle] at hj
        omega
      subst j
      exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start)
  have hdw : d.work 0 = exhausted skipped.length := by
    apply Tape.ext
    · change (d.work 0).head = skipped.length+1
      change (d.work 0).head = 1+skipped.length at wh
      omega
    · exact wc
  refine ⟨placeWorkCfg VerifierFieldSkip.machine 0 1 (before skipped.length) d,
    _, le_rfl, ?_, hh, hin, ?_, hout⟩
  · change skip.reachesIn _
      (placeWorkCfg VerifierFieldSkip.machine 0 1 (before skipped.length) c) _ at hplaced
    simpa only [he] using hplaced
  · funext j
    fin_cases j <;> simp [placeWorkCfg, placeWorkInMiddle, placeWorkCoord, middle, before, hdw]

/-- The field at index skipped.length is returned as a canonical binary word
on work1. The unary index on work0 is exhausted but retains all its cells. -/
theorem indexed_field_hoare (skipped : List (List Bool)) (field suffix : List Bool)
    (out₀ : Tape) (ho : out₀.read ≠ .start) (hoHead : 1 ≤ out₀.head) :
    machine.HoareTime
      (fun inp work out => inp.HasBinarySuffix
        (BinaryFields.encode skipped ++ (BinaryFields.encodeField field ++ suffix)) ∧
        work = before skipped.length ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix suffix ∧
        work = after skipped.length field ∧ out = out₀)
      ((BinaryFields.encode skipped).length+skipped.length+3*field.length+7) := by
  have allmid : ∀ j, (middle skipped.length j).read ≠ .start := by
    intro j
    fin_cases j
    · exact exhausted_off _
    · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start
  have first := skip_hoare skipped (BinaryFields.encodeField field ++ suffix) out₀ ho
  have second := VerifierFieldPlacement.field_hoare 1 0 field suffix (middle skipped.length)
    out₀ rfl (fun j _ => allmid j) ho hoHead
  have he : Function.update (middle skipped.length) (VerifierFieldPlacement.slot 1 0)
      (wordTape field) = after skipped.length field := by
    funext j
    fin_cases j <;> simp [middle, after, VerifierFieldPlacement.slot, placeWorkIdx]
  have second' : (VerifierFieldPlacement.machine 1 0).HoareTime
      (fun inp work out => inp.HasBinarySuffix (BinaryFields.encodeField field ++ suffix) ∧
        work = middle skipped.length ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix suffix ∧ work = after skipped.length field ∧ out = out₀)
      (3*field.length+5) := by simpa only [he] using second
  have stable : ∀ inp work out,
      (inp.HasBinarySuffix (BinaryFields.encodeField field ++ suffix) ∧
        work = middle skipped.length ∧ out = out₀) →
      (transitionInput inp).HasBinarySuffix (BinaryFields.encodeField field ++ suffix) ∧
        (fun j => transitionTape (work j)) = middle skipped.length ∧ transitionTape out = out₀ := by
    rintro inp work out ⟨hi, rfl, rfl⟩
    obtain ⟨hin, hw, hout⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start allmid ho
    exact ⟨by simpa only [hin] using hi, hw, hout⟩
  exact (seqTM_hoareTime _ _ first stable second').mono_bound (by omega)

end UnconstrainedPACDetection.VerifierIndexedField

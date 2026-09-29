module

public import proofs.UnconstrainedPACDetection.VerifierSignToken

@[expose] public section

/-! Indexed signed-field extraction: separate sign and magnitude without
copying or shifting a parsed signed word. -/
namespace UnconstrainedPACDetection.VerifierSignedField
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierIndexedField (counter exhausted exhausted_off)

def before (k : ℕ) : Fin 3 → Tape := ![counter k, wordTape [], wordTape []]
def skippedFrame (k : ℕ) : Fin 3 → Tape := ![exhausted k, wordTape [], wordTape []]
def signedFrame (k : ℕ) (sign : Bool) : Fin 3 → Tape := ![exhausted k, wordTape [], wordTape [sign]]
def after (k : ℕ) (sign : Bool) (mag : List Bool) : Fin 3 → Tape :=
  ![exhausted k, wordTape mag, wordTape [sign]]
def skip : TM 3 := placeWorkTM 0 2 VerifierFieldSkip.machine
def readSign : TM 3 := placeWorkTM 2 0 VerifierSignToken.machine
def machine : TM 3 := seqTM skip (seqTM readSign (VerifierFieldPlacement.machine 1 1))

theorem skip_hoare (fields : List (List Bool)) (suffix : List Bool) (out₀ : Tape)
    (ho : out₀.read ≠ .start) :
    skip.HoareTime
      (fun inp work out => inp.HasBinarySuffix (BinaryFields.encode fields ++ suffix) ∧ work = before fields.length ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix suffix ∧ work = skippedFrame fields.length ∧ out = out₀)
      ((BinaryFields.encode fields).length+fields.length+1) := by
  rintro inp work out ⟨hi, rfl, rfl⟩
  let c : Cfg 1 (Fin 4) := ⟨0, inp, fun _ => counter fields.length, out⟩
  obtain ⟨d, hd, hh, hin, hw, ih, wh, ic, wc, hout⟩ :=
    VerifierFieldSkip.skip_run fields suffix c rfl hi
      (Tape.init_move_right_hasBinaryString _).hasBinarySuffix ho
  have he : placeWorkCfg VerifierFieldSkip.machine 0 2 (before fields.length) c =
      (⟨skip.qstart, inp, before fields.length, out⟩ : Cfg 3 skip.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [placeWorkCfg, placeWorkInMiddle, c, before]
    · rfl
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierFieldSkip.machine 0 2 (before fields.length) hd (by
      intro j hj
      fin_cases j
      · simp [placeWorkInMiddle] at hj
      · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start
      · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start)
  have hdw : d.work 0 = exhausted fields.length := by
    apply Tape.ext
    · change (d.work 0).head = fields.length+1
      change (d.work 0).head = 1+fields.length at wh
      omega
    · exact wc
  refine ⟨placeWorkCfg VerifierFieldSkip.machine 0 2 (before fields.length) d,
    _, le_rfl, ?_, hh, hin, ?_, hout⟩
  · change skip.reachesIn _ (placeWorkCfg VerifierFieldSkip.machine 0 2 (before fields.length) c) _ at hp
    simpa only [he] using hp
  · funext j
    fin_cases j <;> simp [placeWorkCfg, placeWorkInMiddle, placeWorkCoord, skippedFrame, before, hdw]

theorem sign_hoare (k : ℕ) (sign : Bool) (rest : List Bool) (out₀ : Tape)
    (ho : out₀.read ≠ .start) :
    readSign.HoareTime
      (fun inp work out => inp.HasBinarySuffix (true :: sign :: rest) ∧ work = skippedFrame k ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix rest ∧ work = signedFrame k sign ∧ out = out₀) 2 := by
  rintro inp work out ⟨hi, rfl, rfl⟩
  let c : Cfg 1 (Fin 3) := ⟨0, inp, fun _ => wordTape [], out⟩
  obtain ⟨d, t, hb, hd, hh, hin, hw, hout⟩ :=
    VerifierSignToken.sign_hoare sign rest out ho inp (fun _ => wordTape []) out ⟨hi, rfl, rfl⟩
  have he : placeWorkCfg VerifierSignToken.machine 2 0 (skippedFrame k) c =
      (⟨readSign.qstart, inp, skippedFrame k, out⟩ : Cfg 3 readSign.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [placeWorkCfg, placeWorkInMiddle, c, skippedFrame]
    · rfl
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierSignToken.machine 2 0 (skippedFrame k) hd (by
      intro j hj
      fin_cases j
      · exact exhausted_off k
      · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start
      · simp [placeWorkInMiddle] at hj)
  refine ⟨placeWorkCfg VerifierSignToken.machine 2 0 (skippedFrame k) d,
    t, hb, ?_, hh, hin, ?_, hout⟩
  · change readSign.reachesIn t (placeWorkCfg VerifierSignToken.machine 2 0 (skippedFrame k) c) _ at hp
    simpa only [he] using hp
  · funext j
    fin_cases j <;> simp [placeWorkCfg, placeWorkInMiddle, placeWorkCoord, signedFrame, skippedFrame, hw]

theorem stable (suffix : List Bool) (frame : Fin 3 → Tape) (out₀ : Tape)
    (hf : ∀ j, (frame j).read ≠ .start) (ho : out₀.read ≠ .start) :
    ∀ inp work out, (inp.HasBinarySuffix suffix ∧ work = frame ∧ out = out₀) →
      (transitionInput inp).HasBinarySuffix suffix ∧
        (fun j => transitionTape (work j)) = frame ∧ transitionTape out = out₀ := by
  rintro inp work out ⟨hi, rfl, rfl⟩
  obtain ⟨hin, hw, hout⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start hf ho
  exact ⟨by simpa only [hin] using hi, hw, hout⟩

theorem signed_field_hoare (fields : List (List Bool)) (sign : Bool) (mag suffix : List Bool)
    (out₀ : Tape) (ho : out₀.read ≠ .start) (hoHead : 1 ≤ out₀.head) :
    machine.HoareTime
      (fun inp work out => inp.HasBinarySuffix
        (BinaryFields.encode fields ++ (BinaryFields.encodeField (sign :: mag) ++ suffix)) ∧
        work = before fields.length ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix suffix ∧ work = after fields.length sign mag ∧ out = out₀)
      ((BinaryFields.encode fields).length+fields.length+3*mag.length+10) := by
  have offSkip : ∀ j, (skippedFrame fields.length j).read ≠ .start := by
    intro j
    fin_cases j
    · exact exhausted_off _
    · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start
    · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start
  have offSign : ∀ j, (signedFrame fields.length sign j).read ≠ .start := by
    intro j
    fin_cases j
    · exact exhausted_off _
    · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start
    · exact (Tape.init_move_right_hasBinaryString [sign]).hasBinarySuffix.read_ne_start
  have parse := VerifierFieldPlacement.field_hoare 1 1 mag suffix (signedFrame fields.length sign)
    out₀ rfl (fun j _ => offSign j) ho hoHead
  have he : Function.update (signedFrame fields.length sign) (VerifierFieldPlacement.slot 1 1)
      (wordTape mag) = after fields.length sign mag := by
    funext j
    fin_cases j <;> simp [signedFrame, after, VerifierFieldPlacement.slot, placeWorkIdx]
  have parse' : (VerifierFieldPlacement.machine 1 1).HoareTime
      (fun inp work out => inp.HasBinarySuffix (BinaryFields.encodeField mag ++ suffix) ∧ work = signedFrame fields.length sign ∧ out = out₀)
      (fun inp work out => inp.HasBinarySuffix suffix ∧ work = after fields.length sign mag ∧ out = out₀)
      (3*mag.length+5) := by simpa only [he] using parse
  have tail := seqTM_hoareTime _ _ (sign_hoare fields.length sign (BinaryFields.encodeField mag ++ suffix) out₀ ho)
    (stable _ _ out₀ offSign ho) parse'
  have first := skip_hoare fields (true :: sign :: (BinaryFields.encodeField mag ++ suffix)) out₀ ho
  have whole := seqTM_hoareTime _ _ first (stable _ _ out₀ offSkip ho) tail
  have result := whole.mono_bound (show
    (BinaryFields.encode fields).length+fields.length+1+1+(2+1+(3*mag.length+5)) ≤
      (BinaryFields.encode fields).length+fields.length+3*mag.length+10 by omega)
  simpa only [machine, BinaryFields.encodeField, List.cons_append] using result

end UnconstrainedPACDetection.VerifierSignedField

module

public import proofs.UnconstrainedPACDetection.VerifierSignedWitnessField
public import proofs.UnconstrainedPACDetection.VerifierSelectedProduct

@[expose] public section

/-! Actual saved signed-field extraction followed by multiplication. -/
namespace UnconstrainedPACDetection.VerifierWitnessProduct
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierIndexedField (counter exhausted exhausted_off)

def initial (xs : List Bool) (k : ℕ) (wit : Tape) : Fin 7 → Tape :=
  ![wordTape xs, counter k, wordTape [], wordTape [], wit, wordTape [], wordTape []]
def ready (xs : List Bool) (k : ℕ) (sign : Bool) (mag prod : List Bool) (wit : Tape) : Fin 7 → Tape :=
  ![wordTape xs, exhausted k, wordTape mag, wordTape [sign], wit, wordTape prod, wordTape []]
def result (xs : List Bool) (k : ℕ) (sign : Bool) (mag prod suffix : List Bool)
    (wit₀ inp₀ out₀ : Tape) : Tape → (Fin 7 → Tape) → Tape → Prop :=
  fun inp work out => inp = inp₀ ∧ ∃ wit, wit.HasBinarySuffix suffix ∧
    wit.cells = wit₀.cells ∧ work = ready xs k sign mag prod wit ∧ out = out₀
def extract : TM 7 := placeWorkTM 0 2 VerifierSignedWitnessField.machine
def machine : TM 7 := seqTM extract VerifierSelectedProduct.machine

theorem extract_hoare (fields : List (List Bool)) (xs : List Bool) (sign : Bool)
    (mag suffix : List Bool) (wit₀ inp₀ out₀ : Tape)
    (hi : wit₀.HasBinarySuffix (BinaryFields.encode fields ++ (BinaryFields.encodeField (sign :: mag) ++ suffix)))
    (hm : wit₀.StartInvariant) (hr : inp₀.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoHead : 1 ≤ out₀.head) :
    extract.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initial xs fields.length wit₀ ∧ out = out₀)
      (result xs fields.length sign mag [] suffix wit₀ inp₀ out₀)
      ((BinaryFields.encode fields).length+fields.length+3*mag.length+10) := by
  rintro inp work out ⟨rfl, rfl, rfl⟩
  let s : Cfg 5 VerifierSignedWitnessField.machine.Q :=
    ⟨VerifierSignedWitnessField.machine.qstart, inp,
      ![wordTape xs, counter fields.length, wordTape [], wordTape [], wit₀], out⟩
  obtain ⟨t,d,hb,hd,hh,hc,hk,hmag,hsg,hwit,hwc,hin,hout⟩ :=
    VerifierSignedWitnessField.extraction_run fields sign mag suffix s rfl
      (Tape.init_move_right_hasBinaryString xs).hasBinarySuffix.read_ne_start
      rfl rfl rfl hi hm hr ho hoHead
  have he : placeWorkCfg VerifierSignedWitnessField.machine 0 2 (initial xs fields.length wit₀) s =
      (⟨extract.qstart, inp, initial xs fields.length wit₀, out⟩ : Cfg 7 extract.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [placeWorkCfg, placeWorkInMiddle, placeWorkCoord, s, initial]
    · rfl
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierSignedWitnessField.machine 0 2 (initial xs fields.length wit₀) hd (by
      intro j hj
      fin_cases j
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start
      · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start)
  refine ⟨placeWorkCfg VerifierSignedWitnessField.machine 0 2 (initial xs fields.length wit₀) d,
    t, hb, ?_, hh, hin, d.work 4, hwit, hwc, ?_, hout⟩
  · change extract.reachesIn t
      (placeWorkCfg VerifierSignedWitnessField.machine 0 2 (initial xs fields.length wit₀) s) _ at hp
    simpa only [he] using hp
  · funext j
    fin_cases j <;> simp [placeWorkCfg, placeWorkInMiddle, placeWorkCoord, initial, ready,
      hc, hk, hmag, hsg, s]

theorem ready_off (xs : List Bool) (k : ℕ) (sign : Bool) (mag prod suffix : List Bool)
    (wit : Tape) (hi : wit.HasBinarySuffix suffix) :
    ∀ j, (ready xs k sign mag prod wit j).read ≠ .start := by
  intro j
  fin_cases j
  · exact (Tape.init_move_right_hasBinaryString xs).hasBinarySuffix.read_ne_start
  · exact exhausted_off k
  · exact (Tape.init_move_right_hasBinaryString mag).hasBinarySuffix.read_ne_start
  · exact (Tape.init_move_right_hasBinaryString [sign]).hasBinarySuffix.read_ne_start
  · exact hi.read_ne_start
  · exact (Tape.init_move_right_hasBinaryString prod).hasBinarySuffix.read_ne_start
  · exact (Tape.init_move_right_hasBinaryString []).hasBinarySuffix.read_ne_start

theorem product_hoare (xs : List Bool) (k : ℕ) (sign : Bool) (mag suffix : List Bool)
    (wit₀ inp₀ out₀ : Tape) (hr : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) :
    VerifierSelectedProduct.machine.HoareTime
      (result xs k sign mag [] suffix wit₀ inp₀ out₀)
      (result xs k sign mag (VerifierBinaryProduct.multiply xs mag) suffix wit₀ inp₀ out₀)
      (mag.length+2+mag.length*(10*xs.length+20*mag.length+30)) := by
  rintro inp work out ⟨rfl, wit, hi, hc, rfl, rfl⟩
  let c : Cfg 7 VerifierSelectedProduct.machine.Q :=
    ⟨VerifierSelectedProduct.machine.qstart, inp, ready xs k sign mag [] wit, out⟩
  obtain ⟨t,d,hb,hd,hh,hw,hin,hout⟩ := VerifierSelectedProduct.multiplication_run xs mag c rfl
    (Tape.init_move_right_hasBinaryString xs) ((Tape.StartInvariant.init_ofBool xs).move .right)
    (Tape.init_move_right_hasBinaryString mag) ((Tape.StartInvariant.init_ofBool mag).move .right)
    rfl rfl (fun j _ => ready_off xs k sign mag [] suffix wit hi j) hr ho
  refine ⟨d,t,hb,hd,hh,hin,wit,hi,hc,?_,hout⟩
  rw [hw]
  funext j
  fin_cases j <;> simp [c, ready]

/-- Extraction and product are one actual machine, with its connecting
transition charged and both caller tapes fixed throughout. -/
theorem witness_product_hoare (fields : List (List Bool)) (xs : List Bool) (sign : Bool)
    (mag suffix : List Bool) (wit₀ inp₀ out₀ : Tape)
    (hi : wit₀.HasBinarySuffix (BinaryFields.encode fields ++ (BinaryFields.encodeField (sign :: mag) ++ suffix)))
    (hm : wit₀.StartInvariant) (hr : inp₀.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoHead : 1 ≤ out₀.head) :
    machine.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initial xs fields.length wit₀ ∧ out = out₀)
      (result xs fields.length sign mag (VerifierBinaryProduct.multiply xs mag) suffix wit₀ inp₀ out₀)
      ((BinaryFields.encode fields).length+fields.length+4*mag.length+13+
        mag.length*(10*xs.length+20*mag.length+30)) := by
  have stable : ∀ inp work out, result xs fields.length sign mag [] suffix wit₀ inp₀ out₀ inp work out →
      result xs fields.length sign mag [] suffix wit₀ inp₀ out₀ (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
    rintro inp work out ⟨rfl, wit, hwi, hwc, rfl, rfl⟩
    obtain ⟨hin, hw, hout⟩ := phaseTransition_eq_self_of_reads_ne_start hr
      (ready_off xs fields.length sign mag [] suffix wit hwi) ho
    exact ⟨hin,wit,hwi,hwc,hw,hout⟩
  have h := seqTM_hoareTime _ _ (extract_hoare fields xs sign mag suffix wit₀ inp₀ out₀ hi hm hr ho hoHead)
    stable (product_hoare xs fields.length sign mag suffix wit₀ inp₀ out₀ hr ho)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierWitnessProduct

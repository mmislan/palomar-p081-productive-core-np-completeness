module

public import proofs.UnconstrainedPACDetection.VerifierWitnessProduct
public import proofs.UnconstrainedPACDetection.VerifierSignedAccumulate

@[expose] public section

/-! Selected signed witness product followed by its contribution to two totals. -/
namespace UnconstrainedPACDetection.VerifierSignedContribution
open Complexity
open Complexity.TM
open VerifierBufferedProduct (wordTape)

def extend (w : Fin 7 → Tape) (pos neg : List Bool) : Fin 9 → Tape :=
  ![w 0,w 1,w 2,w 3,w 4,w 5,w 6,wordTape pos,wordTape neg]

def stage : TM 9 := placeWorkTM 0 2 VerifierWitnessProduct.machine
def machine (isRight : Bool) : TM 9 := seqTM stage (VerifierSignedAccumulate.machine isRight)

def ready (xs : List Bool) (k : ℕ) (sign : Bool) (mag prod pos neg : List Bool)
    (wit : Tape) : Fin 9 → Tape := extend (VerifierWitnessProduct.ready xs k sign mag prod wit) pos neg

def result (xs : List Bool) (k : ℕ) (sign : Bool) (mag prod pos neg suffix : List Bool)
    (wit₀ inp₀ out₀ : Tape) : Tape → (Fin 9 → Tape) → Tape → Prop :=
  fun inp work out => inp = inp₀ ∧ ∃ wit, wit.HasBinarySuffix suffix ∧
    wit.cells = wit₀.cells ∧ work = ready xs k sign mag prod pos neg wit ∧ out = out₀

theorem ready_off (xs : List Bool) (k : ℕ) (sign : Bool) (mag prod pos neg suffix : List Bool)
    (wit : Tape) (hi : wit.HasBinarySuffix suffix) :
    ∀ j, (ready xs k sign mag prod pos neg wit j).read ≠ .start := by
  intro j
  fin_cases j
  · exact VerifierWitnessProduct.ready_off xs k sign mag prod suffix wit hi 0
  · exact VerifierWitnessProduct.ready_off xs k sign mag prod suffix wit hi 1
  · exact VerifierWitnessProduct.ready_off xs k sign mag prod suffix wit hi 2
  · exact VerifierWitnessProduct.ready_off xs k sign mag prod suffix wit hi 3
  · exact VerifierWitnessProduct.ready_off xs k sign mag prod suffix wit hi 4
  · exact VerifierWitnessProduct.ready_off xs k sign mag prod suffix wit hi 5
  · exact VerifierWitnessProduct.ready_off xs k sign mag prod suffix wit hi 6
  · exact (Tape.init_move_right_hasBinaryString pos).hasBinarySuffix.read_ne_start
  · exact (Tape.init_move_right_hasBinaryString neg).hasBinarySuffix.read_ne_start

theorem stage_hoare (fields : List (List Bool)) (xs : List Bool) (sign : Bool)
    (mag pos neg suffix : List Bool) (wit₀ inp₀ out₀ : Tape)
    (hi : wit₀.HasBinarySuffix (BinaryFields.encode fields ++ (BinaryFields.encodeField (sign :: mag) ++ suffix)))
    (hm : wit₀.StartInvariant) (hr : inp₀.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoHead : 1 ≤ out₀.head) :
    stage.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = extend (VerifierWitnessProduct.initial xs fields.length wit₀) pos neg ∧ out = out₀)
      (result xs fields.length sign mag (VerifierBinaryProduct.multiply xs mag) pos neg suffix wit₀ inp₀ out₀)
      ((BinaryFields.encode fields).length+fields.length+4*mag.length+13+
        mag.length*(10*xs.length+20*mag.length+30)) := by
  rintro inp work out ⟨rfl,rfl,rfl⟩
  let w := VerifierWitnessProduct.initial xs fields.length wit₀
  obtain ⟨d,t,hb,hd,hh,hin,wit,hwi,hwc,hw,hout⟩ :=
    VerifierWitnessProduct.witness_product_hoare fields xs sign mag suffix wit₀ inp out hi hm hr ho hoHead
      inp w out ⟨rfl,rfl,rfl⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierWitnessProduct.machine 0 2 (extend w pos neg) hd (by
      intro j hj
      fin_cases j
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · simp [placeWorkInMiddle] at hj
      · exact (Tape.init_move_right_hasBinaryString pos).hasBinarySuffix.read_ne_start
      · exact (Tape.init_move_right_hasBinaryString neg).hasBinarySuffix.read_ne_start)
  have he : placeWorkCfg VerifierWitnessProduct.machine 0 2 (extend w pos neg)
      ⟨VerifierWitnessProduct.machine.qstart,inp,w,out⟩ =
      (⟨stage.qstart,inp,extend w pos neg,out⟩ : Cfg 9 stage.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,extend]
    · rfl
  refine ⟨placeWorkCfg VerifierWitnessProduct.machine 0 2 (extend w pos neg) d,t,hb,?_,hh,hin,wit,hwi,hwc,?_,hout⟩
  · change stage.reachesIn _ _ _ at hp
    simpa only [he] using hp
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,extend,ready,hw]

def newPos (b : Bool) (term pos : List Bool) : List Bool :=
  if b then VerifierBinaryAdd.add false term pos else pos

def newNeg (b : Bool) (term neg : List Bool) : List Bool :=
  if b then neg else VerifierBinaryAdd.add false term neg

def addBound (term pos neg : List Bool) : ℕ :=
  term.length + 2 * max term.length (max pos.length neg.length) + 8

theorem accumulation_hoare (isRight : Bool) (xs : List Bool) (k : ℕ) (sign : Bool)
    (mag prod pos neg suffix : List Bool) (wit₀ inp₀ out₀ : Tape)
    (hr : inp₀.read ≠ .start) (ho : out₀.read ≠ .start) :
    (VerifierSignedAccumulate.machine isRight).HoareTime
      (result xs k sign mag prod pos neg suffix wit₀ inp₀ out₀)
      (result xs k sign mag prod (newPos (xor isRight sign) prod pos)
        (newNeg (xor isRight sign) prod neg) suffix wit₀ inp₀ out₀)
      (addBound prod pos neg) := by
  rintro inp work out ⟨rfl,wit,hwi,hwc,rfl,rfl⟩
  let c : Cfg 9 VerifierSignedAccumulate.Q :=
    ⟨some none,inp,ready xs k sign mag prod pos neg wit,out⟩
  let total := if xor isRight sign then pos else neg
  have ht : (c.work (VerifierTotalBranch.target (xor isRight sign))).HasBinaryString total := by
    cases isRight <;> cases sign <;> exact Tape.init_move_right_hasBinaryString _
  have htm : (c.work (VerifierTotalBranch.target (xor isRight sign))).cells 0 = .start := by
    cases isRight <;> cases sign <;> rfl
  obtain ⟨d,hd,hh,hw,hin,hout⟩ := VerifierSignedAccumulate.accumulation_run isRight sign prod total c rfl
    (Tape.init_move_right_hasBinaryString [sign]) (Tape.init_move_right_hasBinaryString prod)
    ((Tape.StartInvariant.init_ofBool prod).move .right) ht htm
    (ready_off xs k sign mag prod pos neg suffix wit hwi) hr ho
  refine ⟨d,_,?_,hd,hh,hin,wit,hwi,hwc,?_,hout⟩
  · have ha := VerifierBinaryAdd.add_length false prod total
    have htlen : total.length ≤ max pos.length neg.length := by
      dsimp [total]
      split <;> omega
    dsimp [addBound]
    omega
  · rw [hw]
    funext j
    cases isRight <;> cases sign <;> fin_cases j <;>
      simp [c, ready, extend, VerifierWitnessProduct.ready, VerifierTotalBranch.target,
        newPos, newNeg, total]

/-- One actual machine extracts a signed field, multiplies by the selected
coefficient, and adds the product to exactly the appropriate unsigned total. -/
theorem contribution_hoare (isRight : Bool) (fields : List (List Bool)) (xs : List Bool) (sign : Bool)
    (mag pos neg suffix : List Bool) (wit₀ inp₀ out₀ : Tape)
    (hi : wit₀.HasBinarySuffix (BinaryFields.encode fields ++ (BinaryFields.encodeField (sign :: mag) ++ suffix)))
    (hm : wit₀.StartInvariant) (hr : inp₀.read ≠ .start)
    (ho : out₀.read ≠ .start) (hoHead : 1 ≤ out₀.head) :
    (machine isRight).HoareTime
      (fun inp work out => inp = inp₀ ∧ work = extend (VerifierWitnessProduct.initial xs fields.length wit₀) pos neg ∧ out = out₀)
      (result xs fields.length sign mag (VerifierBinaryProduct.multiply xs mag)
        (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos)
        (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg)
        suffix wit₀ inp₀ out₀)
      ((BinaryFields.encode fields).length+fields.length+4*mag.length+14+
        mag.length*(10*xs.length+20*mag.length+30)+
        addBound (VerifierBinaryProduct.multiply xs mag) pos neg) := by
  have stable : ∀ inp work out,
      result xs fields.length sign mag (VerifierBinaryProduct.multiply xs mag) pos neg suffix wit₀ inp₀ out₀ inp work out →
      result xs fields.length sign mag (VerifierBinaryProduct.multiply xs mag) pos neg suffix wit₀ inp₀ out₀
        (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
    rintro inp work out ⟨rfl,wit,hwi,hwc,rfl,rfl⟩
    obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start hr
      (ready_off xs fields.length sign mag (VerifierBinaryProduct.multiply xs mag) pos neg suffix wit hwi) ho
    exact ⟨hin,wit,hwi,hwc,hw,hout⟩
  have h := seqTM_hoareTime _ _
    (stage_hoare fields xs sign mag pos neg suffix wit₀ inp₀ out₀ hi hm hr ho hoHead)
    stable (accumulation_hoare isRight xs fields.length sign mag (VerifierBinaryProduct.multiply xs mag)
      pos neg suffix wit₀ inp₀ out₀ hr ho)
  exact h.mono_bound (by omega)

/-- The two unsigned totals implement the intended signed coefficient-flow term. -/
theorem contribution_value (isRight sign : Bool) (xs mag pos neg : List Bool) :
    (BinaryFields.readNat (newPos (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) pos) : ℤ) -
      BinaryFields.readNat (newNeg (xor isRight sign) (VerifierBinaryProduct.multiply xs mag) neg) =
    (BinaryFields.readNat pos : ℤ) - BinaryFields.readNat neg +
      (if isRight then (1 : ℤ) else -1) * (if sign then (-1 : ℤ) else 1) *
        BinaryFields.readNat xs * BinaryFields.readNat mag := by
  cases isRight <;> cases sign <;>
    simp [newPos, newNeg, VerifierBinaryAdd.add_value, VerifierBinaryProduct.multiply_value]
  all_goals ring

end UnconstrainedPACDetection.VerifierSignedContribution

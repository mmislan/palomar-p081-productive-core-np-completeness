module

public import proofs.UnconstrainedPACDetection.VerifierFieldParser

@[expose] public section

/-! Binary addition for the PAC verifier: finite carry state, no iteration
over the numerical value of an operand. Operands are little endian. -/
namespace UnconstrainedPACDetection.VerifierBinaryAdd
open Complexity
open Complexity.TM

def digit (a b c : Bool) : Bool := xor (xor a b) c
def carry (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

def add (c : Bool) : List Bool → List Bool → List Bool
  | [], [] => if c then [true] else []
  | a :: xs, [] => digit a false c :: add (carry a false c) xs []
  | [], b :: ys => digit false b c :: add (carry false b c) [] ys
  | a :: xs, b :: ys => digit a b c :: add (carry a b c) xs ys

theorem add_value (c : Bool) (xs ys : List Bool) :
    BinaryFields.readNat (add c xs ys) =
      BinaryFields.readNat xs + BinaryFields.readNat ys + c.toNat := by
  cases xs with
  | nil =>
    cases ys with
    | nil => cases c <;> simp [add, BinaryFields.readNat]
    | cons b ys =>
      have ih := add_value (carry false b c) [] ys
      cases b <;> cases c <;>
        simp_all [add, BinaryFields.readNat, digit, carry, Nat.bit, Bool.toNat]
      all_goals omega
  | cons a xs =>
    cases ys with
    | nil =>
      have ih := add_value (carry a false c) xs []
      cases a <;> cases c <;>
        simp_all [add, BinaryFields.readNat, digit, carry, Nat.bit, Bool.toNat]
      all_goals omega
    | cons b ys =>
      have ih := add_value (carry a b c) xs ys
      cases a <;> cases b <;> cases c <;>
        simp_all [add, BinaryFields.readNat, digit, carry, Nat.bit, Bool.toNat]
      all_goals omega
termination_by xs.length + ys.length

def advance (g : Γ) : Dir3 := if g = .blank then .stay else .right
def bit (g : Γ) : Bool := decide (g = .one)

theorem advance_right {g : Γ} (h : g = .start) : advance g = .right := by
  simp [advance, h]

def machine : TM 1 where
  Q := Option Bool
  qstart := some false
  qhalt := none
  δ := fun q i w o =>
    match q with
    | none => allIdle none i w o
    | some c =>
      if i = .start ∨ w 0 = .start then
        (some c, fun j => readBackWrite (w j), readBackWrite o,
          idleDir i, fun j => idleDir (w j), idleDir o)
      else if i = .blank ∧ w 0 = .blank then
        (none, fun j => readBackWrite (w j), if c then .one else readBackWrite o,
          idleDir i, fun j => idleDir (w j), if c then .right else idleDir o)
      else
        (some (carry (bit i) (bit (w 0)) c), fun j => readBackWrite (w j),
          readBackWrite (Γ.ofBool (digit (bit i) (bit (w 0)) c)),
          advance i, fun j => advance (w j), .right)
  δ_right_of_start := by
    intro q i w o
    cases q with
    | none => exact rightOfStart_allIdle i w o
    | some c =>
      dsimp only
      split
      · exact rightOfStart_allIdle i w o
      · split
        · refine ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, ?_⟩
          cases c <;> simp [idleDir]
        · exact ⟨advance_right, fun _ => advance_right, fun _ => rfl⟩

theorem suffix_bit {t : Tape} {xs : List Bool} (h : t.HasBinarySuffix xs) :
    bit t.read = xs.headD false := by
  cases xs with
  | nil => simp [h.read_nil, bit]
  | cons b xs => cases b <;> simp [h.read_cons, bit, Γ.ofBool]

theorem suffix_advance {t : Tape} {xs : List Bool} (h : t.HasBinarySuffix xs) :
    (t.move (advance t.read)).HasBinarySuffix xs.tail := by
  cases xs with
  | nil => simpa [advance, h.read_nil, Tape.move] using h
  | cons b xs =>
    have ha : advance t.read = .right := by
      cases b <;> simp [advance, h.read_cons, Γ.ofBool]
    simpa [ha] using h.move_right_cons

theorem scan_step (xs ys : List Bool) (c : Bool) (s : Cfg 1 machine.Q)
    (hs : s.state = some c) (hx : s.input.HasBinarySuffix xs)
    (hy : (s.work 0).HasBinarySuffix ys) (hne : xs ≠ [] ∨ ys ≠ [])
    (emitted : List Bool) (ho : s.output.HasBinaryPrefix emitted) :
    ∃ d, machine.step s = some d ∧
      d.state = some (carry (xs.headD false) (ys.headD false) c) ∧
      d.input.HasBinarySuffix xs.tail ∧ (d.work 0).HasBinarySuffix ys.tail ∧
      d.output.HasBinaryPrefix
        (emitted ++ [digit (xs.headD false) (ys.headD false) c]) := by
  have hnstart : ¬(s.input.read = .start ∨ (s.work 0).read = .start) :=
    not_or.mpr ⟨hx.read_ne_start, hy.read_ne_start⟩
  have hnblank : ¬(s.input.read = .blank ∧ (s.work 0).read = .blank) := by
    rcases hne with h | h
    · cases xs with
      | nil => contradiction
      | cons a xs => cases a <;> simp [hx.read_cons, Γ.ofBool]
    · cases ys with
      | nil => contradiction
      | cons b ys => cases b <;> simp [hy.read_cons, Γ.ofBool]
  let d : Cfg 1 machine.Q :=
    { state := some (carry (bit s.input.read) (bit (s.work 0).read) c)
      input := s.input.move (advance s.input.read)
      work := fun j => (s.work j).writeAndMove (readBackWrite (s.work j).read)
        (advance (s.work j).read)
      output := s.output.writeAndMove
        (readBackWrite (Γ.ofBool (digit (bit s.input.read) (bit (s.work 0).read) c))) .right }
  refine ⟨d, ?_, ?_, suffix_advance hx, ?_, ?_⟩
  · simp [TM.step, machine, hs, hnstart, hnblank, d]
  · simp only [d, suffix_bit hx, suffix_bit hy]
    rfl
  · change ((s.work 0).writeAndMove _ _).HasBinarySuffix ys.tail
    rw [writeAndMove_readBack _ hy.read_ne_start]
    exact suffix_advance hy
  · have hb : (readBackWrite (Γ.ofBool (digit (bit s.input.read) (bit (s.work 0).read) c))).toΓ =
        Γ.ofBool (digit (xs.headD false) (ys.headD false) c) := by
      rw [suffix_bit hx, suffix_bit hy]
      cases digit (xs.headD false) (ys.headD false) c <;> rfl
    simpa only [d, hb] using Tape.hasBinaryPrefix_write_bit
      (digit (xs.headD false) (ys.headD false) c) ho

theorem halt_empty (c : Bool) (s : Cfg 1 machine.Q)
    (hs : s.state = some c) (hx : s.input.HasBinarySuffix [])
    (hy : (s.work 0).HasBinarySuffix [])
    (emitted : List Bool) (ho : s.output.HasBinaryPrefix emitted) :
    ∃ d, machine.reachesIn 1 s d ∧ machine.halted d ∧
      d.output.HasBinaryPrefix (emitted ++ add c [] []) := by
  let d : Cfg 1 machine.Q :=
    { state := none
      input := s.input.move (idleDir s.input.read)
      work := fun j => (s.work j).writeAndMove (readBackWrite (s.work j).read)
        (idleDir (s.work j).read)
      output := s.output.writeAndMove
        (if c then Γ.one else (readBackWrite s.output.read).toΓ)
        (if c then .right else idleDir s.output.read) }
  have step : machine.step s = some d := by
    cases c <;> simp [TM.step, machine, hs, hx.read_nil, hy.read_nil, d]
  refine ⟨d, .step step .zero, rfl, ?_⟩
  cases c with
  | false =>
    have keep : s.output.writeAndMove (readBackWrite s.output.read).toΓ
        (idleDir s.output.read) = s.output :=
      transitionTape_eq_self (by rw [ho.read_blank]; decide)
    simpa only [d, Bool.false_eq_true, ↓reduceIte, keep, add, List.append_nil] using ho
  | true => simpa only [d, ↓reduceIte, add, Γ.ofBool] using Tape.hasBinaryPrefix_write_bit true ho

/-- Two arbitrary binary words, including unequal lengths and padded zeros:
exactly one transition per remaining bit position and one final carry step. -/
theorem boundary (xs ys : List Bool) (c : Bool) (s : Cfg 1 machine.Q)
    (hs : s.state = some c) (hx : s.input.HasBinarySuffix xs)
    (hy : (s.work 0).HasBinarySuffix ys)
    (emitted : List Bool) (ho : s.output.HasBinaryPrefix emitted) :
    ∃ d, machine.reachesIn (max xs.length ys.length + 1) s d ∧ machine.halted d ∧
      d.output.HasBinaryPrefix (emitted ++ add c xs ys) := by
  by_cases hempty : xs = [] ∧ ys = []
  · obtain ⟨rfl, rfl⟩ := hempty
    exact halt_empty c s hs hx hy emitted ho
  · have hne : xs ≠ [] ∨ ys ≠ [] := by tauto
    obtain ⟨s', hstep, hstate, hx', hy', ho'⟩ := scan_step xs ys c s hs hx hy hne emitted ho
    obtain ⟨d, hd, hh, hout⟩ := boundary xs.tail ys.tail
      (carry (xs.headD false) (ys.headD false) c) s' hstate hx' hy' _ ho'
    have hpositive : 0 < xs.length + ys.length := by
      by_contra h
      apply hempty
      exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
    have hlen : max xs.tail.length ys.tail.length + 1 = max xs.length ys.length := by
      simp only [List.length_tail]
      omega
    have hadd : add c xs ys = digit (xs.headD false) (ys.headD false) c ::
        add (carry (xs.headD false) (ys.headD false) c) xs.tail ys.tail := by
      cases xs <;> cases ys
      · simp at hempty
      all_goals simp only [add, List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil]
    refine ⟨d, ?_, hh, ?_⟩
    · simpa only [hlen] using TM.reachesIn.step hstep hd
    · simpa only [hadd, List.append_assoc, List.singleton_append] using hout
termination_by xs.length + ys.length
decreasing_by
  all_goals
    have hpositive : 0 < xs.length + ys.length := by
      by_contra h
      apply hempty
      exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
    simp_wf
    omega

theorem add_length (c : Bool) (xs ys : List Bool) :
    (add c xs ys).length ≤ max xs.length ys.length + 1 := by
  cases xs with
  | nil =>
    cases ys with
    | nil => cases c <;> simp [add]
    | cons b ys =>
      have ih := add_length (carry false b c) [] ys
      simp only [add, List.length_cons, List.length_nil] at *
      omega
  | cons a xs =>
    cases ys with
    | nil =>
      have ih := add_length (carry a false c) xs []
      simp only [add, List.length_cons, List.length_nil] at *
      omega
    | cons b ys =>
      have ih := add_length (carry a b c) xs ys
      simp only [add, List.length_cons] at *
      omega
termination_by xs.length + ys.length

end UnconstrainedPACDetection.VerifierBinaryAdd


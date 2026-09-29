module

public import proofs.UnconstrainedPACDetection.VerifierBinaryAdd
public import proofs.UnconstrainedPACDetection.VerifierUnsignedTotals

@[expose] public section

/-! Little-endian unsigned comparison: the highest differing bit wins.
No canonical trimming or numerical-value loop is required. -/
namespace UnconstrainedPACDetection.VerifierBinaryCompare
open Complexity
open Complexity.TM
open VerifierBinaryAdd (bit advance advance_right suffix_bit suffix_advance)

def next (a b prior : Bool) : Bool := if a = b then prior else a

def compare (prior : Bool) : List Bool → List Bool → Bool
  | [], [] => prior
  | a :: xs, [] => compare (next a false prior) xs []
  | [], b :: ys => compare (next false b prior) [] ys
  | a :: xs, b :: ys => compare (next a b prior) xs ys

theorem compare_spec (prior : Bool) (xs ys : List Bool) :
    compare prior xs ys = true ↔
      BinaryFields.readNat ys < BinaryFields.readNat xs ∨
      (BinaryFields.readNat ys = BinaryFields.readNat xs ∧ prior = true) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp [compare, BinaryFields.readNat]
    | cons b ys =>
      have ih := compare_spec (next false b prior) [] ys
      cases b <;> cases prior <;> simp_all [compare, next, BinaryFields.readNat, Nat.bit]
  | cons a xs =>
    cases ys with
    | nil =>
      have ih := compare_spec (next a false prior) xs []
      cases a <;> cases prior <;> simp_all [compare, next, BinaryFields.readNat, Nat.bit]
      all_goals omega
    | cons b ys =>
      have ih := compare_spec (next a b prior) xs ys
      cases a <;> cases b <;> cases prior <;>
        simp_all [compare, next, BinaryFields.readNat, Nat.bit]
      all_goals omega
termination_by xs.length + ys.length

theorem compare_false_iff (xs ys : List Bool) :
    compare false xs ys = true ↔ BinaryFields.readNat ys < BinaryFields.readNat xs := by
  simpa using compare_spec false xs ys

def machine : TM 1 where
  Q := Option Bool
  qstart := some false
  qhalt := none
  δ := fun q i w o =>
    match q with
    | none => allIdle none i w o
    | some prior =>
      if i = .start ∨ w 0 = .start then
        (some prior, fun j => readBackWrite (w j), readBackWrite o,
          idleDir i, fun j => idleDir (w j), idleDir o)
      else if i = .blank ∧ w 0 = .blank then
        (none, fun j => readBackWrite (w j), readBackWrite (Γ.ofBool prior),
          idleDir i, fun j => idleDir (w j), .right)
      else
        (some (next (bit i) (bit (w 0)) prior), fun j => readBackWrite (w j), readBackWrite o,
          advance i, fun j => advance (w j), idleDir o)
  δ_right_of_start := by
    intro q i w o
    cases q with
    | none => exact rightOfStart_allIdle i w o
    | some prior =>
      dsimp only
      split
      · exact rightOfStart_allIdle i w o
      · split
        · exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
        · exact ⟨advance_right, fun _ => advance_right, idleDir_right_of_start⟩

theorem scan_step (xs ys : List Bool) (prior : Bool) (s : Cfg 1 machine.Q)
    (hs : s.state = some prior) (hx : s.input.HasBinarySuffix xs)
    (hy : (s.work 0).HasBinarySuffix ys) (hne : xs ≠ [] ∨ ys ≠ [])
    (emitted : List Bool) (ho : s.output.HasBinaryPrefix emitted) :
    ∃ d, machine.step s = some d ∧
      d.state = some (next (xs.headD false) (ys.headD false) prior) ∧
      d.input.HasBinarySuffix xs.tail ∧ (d.work 0).HasBinarySuffix ys.tail ∧
      d.output.HasBinaryPrefix emitted := by
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
    { state := some (next (bit s.input.read) (bit (s.work 0).read) prior)
      input := s.input.move (advance s.input.read)
      work := fun j => (s.work j).writeAndMove (readBackWrite (s.work j).read)
        (advance (s.work j).read)
      output := s.output.writeAndMove (readBackWrite s.output.read) (idleDir s.output.read) }
  refine ⟨d, ?_, ?_, suffix_advance hx, ?_, ?_⟩
  · simp [TM.step, machine, hs, hnstart, hnblank, d]
  · simp only [d, suffix_bit hx, suffix_bit hy]
    rfl
  · change ((s.work 0).writeAndMove _ _).HasBinarySuffix ys.tail
    rw [writeAndMove_readBack _ hy.read_ne_start]
    exact suffix_advance hy
  · have keep : s.output.writeAndMove (readBackWrite s.output.read).toΓ
        (idleDir s.output.read) = s.output :=
      transitionTape_eq_self (by rw [ho.read_blank]; decide)
    simpa only [d, keep] using ho

theorem halt_empty (prior : Bool) (s : Cfg 1 machine.Q)
    (hs : s.state = some prior) (hx : s.input.HasBinarySuffix [])
    (hy : (s.work 0).HasBinarySuffix [])
    (emitted : List Bool) (ho : s.output.HasBinaryPrefix emitted) :
    ∃ d, machine.reachesIn 1 s d ∧ machine.halted d ∧
      d.output.HasBinaryPrefix (emitted ++ [prior]) := by
  let d : Cfg 1 machine.Q :=
    { state := none
      input := s.input.move (idleDir s.input.read)
      work := fun j => (s.work j).writeAndMove (readBackWrite (s.work j).read)
        (idleDir (s.work j).read)
      output := s.output.writeAndMove (Γ.ofBool prior) .right }
  have step : machine.step s = some d := by
    cases prior <;> simp [TM.step, machine, hs, hx.read_nil, hy.read_nil, d, Γ.ofBool, readBackWrite]
  exact ⟨d, .step step .zero, rfl, Tape.hasBinaryPrefix_write_bit prior ho⟩

theorem boundary (xs ys : List Bool) (prior : Bool) (s : Cfg 1 machine.Q)
    (hs : s.state = some prior) (hx : s.input.HasBinarySuffix xs)
    (hy : (s.work 0).HasBinarySuffix ys)
    (emitted : List Bool) (ho : s.output.HasBinaryPrefix emitted) :
    ∃ d, machine.reachesIn (max xs.length ys.length + 1) s d ∧ machine.halted d ∧
      d.output.HasBinaryPrefix (emitted ++ [compare prior xs ys]) := by
  by_cases hempty : xs = [] ∧ ys = []
  · obtain ⟨rfl, rfl⟩ := hempty
    simpa only [List.length_nil, max_self, Nat.zero_add, compare] using
      halt_empty prior s hs hx hy emitted ho
  · have hne : xs ≠ [] ∨ ys ≠ [] := by tauto
    obtain ⟨s', hstep, hstate, hx', hy', ho'⟩ := scan_step xs ys prior s hs hx hy hne emitted ho
    obtain ⟨d, hd, hh, hout⟩ := boundary xs.tail ys.tail
      (next (xs.headD false) (ys.headD false) prior) s' hstate hx' hy' emitted ho'
    have hpositive : 0 < xs.length + ys.length := by
      by_contra h
      apply hempty
      exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
    have hlen : max xs.tail.length ys.tail.length + 1 = max xs.length ys.length := by
      simp only [List.length_tail]
      omega
    have hcompare : compare prior xs ys =
        compare (next (xs.headD false) (ys.headD false) prior) xs.tail ys.tail := by
      cases xs <;> cases ys
      · simp at hempty
      all_goals simp only [compare, List.headD_cons, List.headD_nil, List.tail_cons, List.tail_nil]
    refine ⟨d, ?_, hh, ?_⟩
    · simpa only [hlen] using TM.reachesIn.step hstep hd
    · simpa only [hcompare] using hout
termination_by xs.length + ys.length
decreasing_by
  all_goals
    have hpositive : 0 < xs.length + ys.length := by
      by_contra h
      apply hempty
      exact ⟨List.length_eq_zero_iff.mp (by omega), List.length_eq_zero_iff.mp (by omega)⟩
    simp_wf
    omega

/-- Exact consumer: compare the two unsigned totals in the existing checker. -/
theorem totals_compare_iff {Entity Reaction : Type*} [Fintype Reaction]
    (source : ReversibleSource Entity Reaction) (flow : Reaction → ℤ) (x : Entity)
    (positive negative : List Bool)
    (hp : BinaryFields.readNat positive = VerifierUnsignedTotals.positiveTotal source flow x)
    (hn : BinaryFields.readNat negative = VerifierUnsignedTotals.negativeTotal source flow x) :
    compare false positive negative = true ↔ 0 < ∑ r, source.netInt r x * flow r := by
  rw [compare_false_iff, hp, hn]
  exact (VerifierUnsignedTotals.productive_iff_compare source flow x).symm

end UnconstrainedPACDetection.VerifierBinaryCompare

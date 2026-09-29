module

public import proofs.UnconstrainedPACDetection.VerifierProductPhases
public import proofs.UnconstrainedPACDetection.VerifierBinaryAddFrames

@[expose] public section

/-! Relate the actual multiplier addition phase to the strengthened adder.
This file is the consumer bridge, not a new arithmetic implementation. -/
namespace UnconstrainedPACDetection.VerifierProductMachine
open Complexity
open Complexity.TM

def addState : Option Bool → State
  | some carryIn => (5, true, carryIn)
  | none => (6, false, false)

def embedAdd (mult out : Tape) (s : Cfg 1 VerifierBinaryAdd.machine.Q) : Cfg 3 machine.Q :=
  { state := addState s.state, input := s.input,
    work := ![mult, s.output, s.work 0], output := out }

/-- Each selected-bit addition transition is exactly an existing adder
transition with its operand/output tapes placed inside the fixed multiplier. -/
theorem embed_add_step (mult out : Tape) (hm : mult.read ≠ .start) (hout : out.read ≠ .start)
    (carryIn : Bool) (s t : Cfg 1 VerifierBinaryAdd.machine.Q)
    (hq : s.state = some carryIn) (hi : s.input.read ≠ .start)
    (hw : (s.work 0).read ≠ .start) (ho : s.output.read ≠ .start)
    (hs : VerifierBinaryAdd.machine.step s = some t) :
    machine.step (embedAdd mult out s) = some (embedAdd mult out t) := by
  have hn : s.state ≠ VerifierBinaryAdd.machine.qhalt := by simp [hq, VerifierBinaryAdd.machine]
  have hns : ¬(s.input.read = .start ∨ (s.work 0).read = .start) := not_or.mpr ⟨hi, hw⟩
  simp only [TM.step, hn, ↓reduceIte] at hs
  simp only [VerifierBinaryAdd.machine, hq, hns, ↓reduceIte] at hs
  split at hs
  · rename_i hb
    cases hs
    have hhalt : (embedAdd mult out s).state ≠ machine.qhalt := by
      simp [embedAdd, addState, hq, machine]
    simp only [TM.step, hhalt, ↓reduceIte]
    simp only [machine, embedAdd, hq, addState, control, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Bool.true_eq_false, false_or, Bool.true_and, markerDir,
      hb.1, hb.2, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · simp [idleDir, Tape.move]
    · funext j
      fin_cases j <;> cases carryIn <;>
        simp [ho, hm, hb.2, idleDir, Tape.move]
      all_goals exact write_readBack _ hm
    · exact transitionTape_eq_self hout
  · rename_i hb
    cases hs
    have hhalt : (embedAdd mult out s).state ≠ machine.qhalt := by
      simp [embedAdd, addState, hq, machine]
    simp only [TM.step, hhalt, ↓reduceIte]
    simp only [machine, embedAdd, hq, addState, control, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Bool.true_eq_false, false_or, Bool.true_and, markerDir, hi, hb, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · simp [VerifierBinaryAdd.digit, VerifierBinaryAdd.carry]
    · rfl
    · funext j
      fin_cases j <;> simp [hw, ho, hm, Tape.move]
      all_goals
        first
        | exact write_readBack _ hm
        | cases VerifierBinaryAdd.digit (VerifierBinaryAdd.bit s.input.read)
            (VerifierBinaryAdd.bit (s.work 0).read) carryIn <;> exact ⟨rfl, rfl⟩
    · exact transitionTape_eq_self hout

theorem embed_add_trace (mult out : Tape) (hm : mult.read ≠ .start) (hout : out.read ≠ .start)
    {n : ℕ} {s t : Cfg 1 VerifierBinaryAdd.machine.Q}
    (h : VerifierBinaryAdd.machine.reachesIn n s t)
    (xs ys emitted : List Bool) (hx : s.input.HasBinarySuffix xs)
    (hy : (s.work 0).HasBinarySuffix ys) (ho : s.output.HasBinaryPrefix emitted) :
    machine.reachesIn n (embedAdd mult out s) (embedAdd mult out t) := by
  induction h generalizing xs ys emitted with
  | zero => exact .zero
  | @step a b n d hs hrest ih =>
    obtain ⟨carryIn, hq⟩ : ∃ carryIn, a.state = some carryIn := by
      have hn := state_ne_qhalt_of_step hs
      cases he : a.state with
      | none => exact False.elim (hn he)
      | some c => exact ⟨c, rfl⟩
    have hoOff : a.output.read ≠ .start := by rw [ho.read_blank]; decide
    have hstep := embed_add_step mult out hm hout carryIn a b hq hx.read_ne_start hy.read_ne_start hoOff hs
    apply TM.reachesIn.step hstep
    by_cases hempty : xs = [] ∧ ys = []
    · obtain ⟨rfl, rfl⟩ := hempty
      obtain ⟨z, hz, _, hop, hxp, hyp, _, _, _, _⟩ :=
        VerifierBinaryAdd.boundary_full [] [] carryIn a hq hx hy emitted ho
      obtain ⟨u, hu, huz⟩ := VerifierBinaryAdd.machine.reachesIn_succ_iff.mp hz
      have he : u = z := by cases huz; rfl
      subst u
      have hbz : b = z := Option.some.inj (hs.symm.trans hu)
      subst z
      exact ih [] [] _ hxp hyp hop
    · have hne : xs ≠ [] ∨ ys ≠ [] := by tauto
      obtain ⟨z, hz, _, hxp, hyp, hop⟩ :=
        VerifierBinaryAdd.scan_step xs ys carryIn a hq hx hy hne emitted ho
      have hbz : b = z := Option.some.inj (hs.symm.trans hz)
      subst z
      exact ih xs.tail ys.tail _ hxp hyp hop

/-- Whole selected-bit addition phase on the actual multiplier, with exact
time and the cursor/content facts needed by its subsequent rewinds. -/
theorem selected_add_run (mult out : Tape) (hm : mult.read ≠ .start) (hout : out.read ≠ .start)
    (xs ys emitted : List Bool) (carryIn : Bool) (s : Cfg 1 VerifierBinaryAdd.machine.Q)
    (hq : s.state = some carryIn) (hx : s.input.HasBinarySuffix xs)
    (hy : (s.work 0).HasBinarySuffix ys) (ho : s.output.HasBinaryPrefix emitted) :
    ∃ d, machine.reachesIn (max xs.length ys.length + 1) (embedAdd mult out s) d ∧
      d.state = (6, false, false) ∧
      (d.work 1).HasBinaryPrefix (emitted ++ VerifierBinaryAdd.add carryIn xs ys) ∧
      d.input.HasBinarySuffix [] ∧ (d.work 2).HasBinarySuffix [] ∧
      d.input.head = s.input.head + xs.length ∧ d.input.cells = s.input.cells ∧
      (d.work 2).head = (s.work 0).head + ys.length ∧ (d.work 2).cells = (s.work 0).cells ∧
      d.work 0 = mult ∧ d.output = out := by
  obtain ⟨t, ht, hh, hp, hi, hw, hih, hic, hwh, hwc⟩ :=
    VerifierBinaryAdd.boundary_full xs ys carryIn s hq hx hy emitted ho
  refine ⟨embedAdd mult out t, embed_add_trace mult out hm hout ht xs ys emitted hx hy ho,
    ?_, hp, hi, hw, hih, hic, hwh, hwc, rfl, rfl⟩
  change addState t.state = (6, false, false)
  change t.state = none at hh
  rw [hh]; rfl

def copyTemporaryBit (c : Cfg 3 machine.Q) (b : Bool) : Cfg 3 machine.Q :=
  { c with work := ![c.work 0, (c.work 1).writeAndMove (Γ.ofBool b) .right,
      (c.work 2).move .right] }

theorem unselected_cons_step (b : Bool) (ys emitted : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (5, false, false))
    (hin : c.input.read ≠ .start) (hm : (c.work 0).read ≠ .start) (hout : c.output.read ≠ .start)
    (hy : (c.work 2).HasBinarySuffix (b :: ys)) (ho : (c.work 1).HasBinaryPrefix emitted) :
    machine.step c = some (copyTemporaryBit c b) := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  have ha : (c.work 1).read ≠ .start := by rw [ho.read_blank]; decide
  have ht : (c.work 2).read ≠ .start := hy.read_ne_start
  cases b <;>
    simp only [TM.step, hn, ↓reduceIte]
  all_goals
    have keep := write_readBack (c.work 2) ht
    simp only [hy.read_cons, Γ.ofBool] at keep
    simp only [machine, hq, control, markerDir, hin, hy.read_cons,
      VerifierBinaryAdd.bit, VerifierBinaryAdd.digit, VerifierBinaryAdd.carry]
    congr 1
    apply Cfg.ext
    · simp [copyTemporaryBit, Γ.ofBool, hq]
    · rfl
    · funext j
      fin_cases j <;>
        simp [copyTemporaryBit, hm, ha, hy.read_cons, Γ.ofBool, VerifierBinaryAdd.advance, Tape.move]
      all_goals
        first
        | exact write_readBack _ hm
        | exact ⟨rfl, rfl⟩
        | exact ⟨congrArg Tape.head keep, congrArg Tape.cells keep⟩
    · exact transitionTape_eq_self hout

theorem unselected_nil_step (emitted : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (5, false, false))
    (hin : c.input.read ≠ .start) (hm : (c.work 0).read ≠ .start) (hout : c.output.read ≠ .start)
    (hy : (c.work 2).HasBinarySuffix []) (ho : (c.work 1).HasBinaryPrefix emitted) :
    machine.step c = some { c with state := (6, false, false) } := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  have allw : ∀ j : Fin 3, (c.work j).read ≠ .start := by
    intro j; fin_cases j
    · exact hm
    · change (c.work 1).read ≠ .start
      rw [ho.read_blank]; decide
    · exact hy.read_ne_start
  simp only [TM.step, hn, ↓reduceIte]
  simp only [machine, hq, control, markerDir, hin, hy.read_nil]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    fin_cases j <;> simp [allw, Tape.move]
    all_goals
      first
      | exact write_readBack _ (allw _)
      | simpa only [hy.read_nil, Γw.toΓ] using write_readBack (c.work 2) (allw 2)
  · exact transitionTape_eq_self hout

/-- With selection false and initial carry false, phase 5 copies the
temporary word in n+1 steps and leaves the input exactly where it was. -/
theorem unselected_add_run (ys emitted : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (5, false, false))
    (hin : c.input.read ≠ .start) (hm : (c.work 0).read ≠ .start) (hout : c.output.read ≠ .start)
    (hy : (c.work 2).HasBinarySuffix ys) (ho : (c.work 1).HasBinaryPrefix emitted) :
    ∃ d, machine.reachesIn (ys.length+1) c d ∧ d.state = (6, false, false) ∧
      (d.work 1).HasBinaryPrefix (emitted ++ ys) ∧ (d.work 2).HasBinarySuffix [] ∧
      (d.work 2).head = (c.work 2).head + ys.length ∧ (d.work 2).cells = (c.work 2).cells ∧
      d.input = c.input ∧ d.work 0 = c.work 0 ∧ d.output = c.output := by
  induction ys generalizing emitted c with
  | nil =>
    have hs := unselected_nil_step emitted c hq hin hm hout hy ho
    refine ⟨_, .step hs .zero, rfl, ?_, hy, ?_, rfl, rfl, rfl, rfl⟩
    · simpa only [List.append_nil] using ho
    · simp
  | cons b ys ih =>
    let s := copyTemporaryBit c b
    have hs : machine.step c = some s := unselected_cons_step b ys emitted c hq hin hm hout hy ho
    have hys : (s.work 2).HasBinarySuffix ys := hy.move_right_cons
    have hos : (s.work 1).HasBinaryPrefix (emitted ++ [b]) := by
      simpa [s, copyTemporaryBit] using Tape.hasBinaryPrefix_write_bit b ho
    obtain ⟨d, hd, hqd, hod, hyd, hhd, hcd, hid, hmd, houtd⟩ :=
      ih (emitted ++ [b]) s hq hin hm hout hys hos
    refine ⟨d, .step hs hd, hqd, ?_, hyd, ?_, hcd, hid, hmd, houtd⟩
    · simpa only [List.append_assoc, List.singleton_append] using hod
    · change (d.work 2).head = ((c.work 2).move .right).head + ys.length at hhd
      simp only [Tape.move, List.length_cons] at *
      omega

theorem add_empty_left (ys : List Bool) : VerifierBinaryAdd.add false [] ys = ys := by
  induction ys with
  | nil => simp [VerifierBinaryAdd.add]
  | cons b ys ih =>
    cases b <;> simp [VerifierBinaryAdd.add, VerifierBinaryAdd.digit, VerifierBinaryAdd.carry, ih]

/-- Both branches of the actual phase-5 entry contract, with caller frames
and exact consumed-head counts. No virtual source configuration is required. -/
theorem addition_run (flag : Bool) (xs ys emitted : List Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (5, flag, false))
    (hx : c.input.HasBinarySuffix xs) (hy : (c.work 2).HasBinarySuffix ys)
    (ho : (c.work 1).HasBinaryPrefix emitted)
    (hm : (c.work 0).read ≠ .start) (hout : c.output.read ≠ .start) :
    ∃ d, machine.reachesIn (max (if flag then xs.length else 0) ys.length + 1) c d ∧
      d.state = (6, false, false) ∧
      (d.work 1).HasBinaryPrefix (emitted ++ VerifierBinaryAdd.add false (if flag then xs else []) ys) ∧
      d.input.HasBinarySuffix (if flag then [] else xs) ∧ (d.work 2).HasBinarySuffix [] ∧
      d.input.head = c.input.head + (if flag then xs.length else 0) ∧ d.input.cells = c.input.cells ∧
      (d.work 2).head = (c.work 2).head + ys.length ∧ (d.work 2).cells = (c.work 2).cells ∧
      d.work 0 = c.work 0 ∧ d.output = c.output := by
  cases flag with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_max, Nat.add_zero, add_empty_left]
    obtain ⟨d, hd, hqd, hp, ht, hh, hc, hi, hm', ho'⟩ :=
      unselected_add_run ys emitted c hq hx.read_ne_start hm hout hy ho
    refine ⟨d, hd, hqd, hp, ?_, ht, congrArg Tape.head hi, congrArg Tape.cells hi,
      hh, hc, hm', ho'⟩
    simpa only [hi] using hx
  | true =>
    simp only [↓reduceIte]
    let s : Cfg 1 VerifierBinaryAdd.machine.Q :=
      { state := some false, input := c.input, work := fun _ => c.work 2, output := c.work 1 }
    have hembed : embedAdd (c.work 0) c.output s = c := by
      apply Cfg.ext
      · exact hq.symm
      · rfl
      · funext j; fin_cases j <;> rfl
      · rfl
    obtain ⟨d, hd, hqd, hp, hi, ht, hih, hic, hth, htc, hm', ho'⟩ :=
      selected_add_run (c.work 0) c.output hm hout xs ys emitted false s rfl hx hy ho
    exact ⟨d, by simpa only [hembed] using hd, hqd, hp, hi, ht, hih, hic, hth, htc, hm', ho'⟩

end UnconstrainedPACDetection.VerifierProductMachine

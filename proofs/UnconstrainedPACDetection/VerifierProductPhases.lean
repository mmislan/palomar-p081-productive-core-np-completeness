module

public import proofs.UnconstrainedPACDetection.VerifierProductMachine

@[expose] public section

/-! Execution proofs for the actual multiplier phases. These are local
contracts on the fixed transition table, not replacement abstract machines. -/
namespace UnconstrainedPACDetection.VerifierProductMachine
open Complexity
open Complexity.TM

def eraseIndex (temporary : Bool) : Fin 3 := if temporary then 2 else 1
def eraseState (temporary flag : Bool) : State :=
  (if temporary then 7 else 3, flag, false)
def eraseNext (temporary flag : Bool) : State :=
  if temporary then (8, false, false) else (4, flag, false)

def replaceWork (c : Cfg 3 machine.Q) (q : State) (idx : Fin 3) (t : Tape) : Cfg 3 machine.Q :=
  { c with state := q, work := Function.update c.work idx t }

def erasedLeft (t : Tape) : Tape := t.writeAndMove .blank .left

def blankAbove (t : Tape) : Prop := ∀ j, t.head < j → t.cells j = .blank

theorem erasedLeft_head (t : Tape) : (erasedLeft t).head = t.head - 1 := by
  simp [erasedLeft, Tape.writeAndMove, Tape.move, Tape.write_head]

theorem erasedLeft_blankAbove {t : Tape} (hh : 0 < t.head) (hb : blankAbove t) :
    blankAbove (erasedLeft t) := by
  intro j hj
  have hn : t.head ≠ 0 := by omega
  simp only [erasedLeft_head] at hj
  simp only [erasedLeft, Tape.writeAndMove, Tape.move, Tape.write, hn, ↓reduceIte]
  by_cases he : j = t.head
  · subst j; simp
  · rw [Function.update_of_ne he]
    exact hb j (by omega)

theorem empty_of_blankAbove {t : Tape} (hh : t.head = 0)
    (hs : t.StartInvariant) (hb : blankAbove t) :
    t.move .right = (Tape.init []).move .right := by
  apply Tape.ext
  · simp [Tape.move, hh]
  · funext j
    cases j with
    | zero => simpa [Tape.move] using hs.1
    | succ j => simpa [Tape.move, Tape.init] using hb (j+1) (by omega)

theorem erase_positive_step (temporary flag : Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = eraseState temporary flag)
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hw : ∀ j, j ≠ eraseIndex temporary → (c.work j).read ≠ .start)
    (ht : (c.work (eraseIndex temporary)).StartInvariant)
    (hh : 0 < (c.work (eraseIndex temporary)).head) :
    machine.step c = some (replaceWork c (eraseState temporary flag) (eraseIndex temporary)
      (erasedLeft (c.work (eraseIndex temporary)))) := by
  have hr := ht.read_ne_start (by omega)
  have hn : c.state ≠ machine.qhalt := by
    cases temporary <;> simp [hq, eraseState, machine]
  have allw : ∀ j, (c.work j).read ≠ .start := by
    intro j
    by_cases hj : j = eraseIndex temporary
    · simpa only [hj] using hr
    · exact hw j hj
  cases temporary <;>
    simp only [eraseState, eraseIndex, Bool.false_eq_true, ↓reduceIte] at *
  all_goals
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, control, markerDir, hin, hr, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;>
        simp [replaceWork, erasedLeft, allw, Tape.move]
      all_goals exact write_readBack _ (allw _)
    · exact transitionTape_eq_self hout

theorem erase_zero_step (temporary flag : Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = eraseState temporary flag)
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hw : ∀ j, j ≠ eraseIndex temporary → (c.work j).read ≠ .start)
    (ht : (c.work (eraseIndex temporary)).StartInvariant)
    (hh : (c.work (eraseIndex temporary)).head = 0) :
    machine.step c = some (replaceWork c (eraseNext temporary flag) (eraseIndex temporary)
      ((c.work (eraseIndex temporary)).move .right)) := by
  have hr : (c.work (eraseIndex temporary)).read = .start := by
    change (c.work (eraseIndex temporary)).cells _ = .start
    rw [hh]; exact ht.1
  have hn : c.state ≠ machine.qhalt := by
    cases temporary <;> simp [hq, eraseState, machine]
  cases temporary <;>
    simp only [eraseState, eraseIndex, eraseNext, Bool.false_eq_true, ↓reduceIte] at *
  all_goals
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, control, markerDir, hin, hr, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;>
        simp [replaceWork, hw, Tape.move]
      all_goals
        first
        | exact write_readBack _ (hw _ (by decide))
        | simp [Tape.write, hh]
    · exact transitionTape_eq_self hout

/-- Both concrete backward-erase phases terminate in exactly h+1 steps,
return a genuinely empty tape at head 1, and preserve all unrelated tapes. -/
theorem erase_run (temporary flag : Bool) (k : ℕ) (c : Cfg 3 machine.Q)
    (hq : c.state = eraseState temporary flag)
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hw : ∀ j, j ≠ eraseIndex temporary → (c.work j).read ≠ .start)
    (ht : (c.work (eraseIndex temporary)).StartInvariant)
    (hh : (c.work (eraseIndex temporary)).head = k)
    (hb : blankAbove (c.work (eraseIndex temporary))) :
    ∃ d, machine.reachesIn (k+1) c d ∧ d.state = eraseNext temporary flag ∧
      d.work (eraseIndex temporary) = (Tape.init []).move .right ∧
      d.input = c.input ∧ d.output = c.output ∧
      ∀ j, j ≠ eraseIndex temporary → d.work j = c.work j := by
  induction k generalizing c with
  | zero =>
    have hs := erase_zero_step temporary flag c hq hin hout hw ht hh
    refine ⟨_, .step hs .zero, rfl, ?_, rfl, rfl, ?_⟩
    · simpa only [replaceWork, Function.update_self] using empty_of_blankAbove hh ht hb
    · intro j hj; simp [replaceWork, hj]
  | succ k ih =>
    have hp : 0 < (c.work (eraseIndex temporary)).head := by omega
    let d := replaceWork c (eraseState temporary flag) (eraseIndex temporary)
      (erasedLeft (c.work (eraseIndex temporary)))
    have hs : machine.step c = some d := erase_positive_step temporary flag c hq hin hout hw ht hp
    have ht' : (d.work (eraseIndex temporary)).StartInvariant := by
      simpa only [d, replaceWork, Function.update_self, erasedLeft, Γw.toΓ] using
        ht.writeAndMove Γw.blank .left
    have hh' : (d.work (eraseIndex temporary)).head = k := by
      simp only [d, replaceWork, Function.update_self, erasedLeft_head, hh]
      omega
    have hb' : blankAbove (d.work (eraseIndex temporary)) := by
      simpa only [d, replaceWork, Function.update_self] using erasedLeft_blankAbove hp hb
    have hw' : ∀ j, j ≠ eraseIndex temporary → (d.work j).read ≠ .start := by
      intro j hj; simpa [d, replaceWork, hj] using hw j hj
    obtain ⟨e, he, hq', htape, hi, ho, hframe⟩ := ih d rfl hin hout hw' ht' hh' hb'
    refine ⟨e, .step hs he, hq', htape, hi, ho, ?_⟩
    intro j hj
    simpa [d, replaceWork, hj] using hframe j hj

theorem rewind_temp_step (flag : Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (4, flag, false))
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hw : ∀ j, j ≠ 2 → (c.work j).read ≠ .start)
    (ht : (c.work 2).StartInvariant) :
    machine.step c = some (replaceWork c
      (if (c.work 2).head = 0 then (5, flag, false) else (4, flag, false)) 2
      ((c.work 2).move (if (c.work 2).head = 0 then .right else .left))) := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  by_cases hh : (c.work 2).head = 0
  · have hr : (c.work 2).read = .start := by
      change (c.work 2).cells _ = .start
      rw [hh]; exact ht.1
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, control, markerDir, hin, hr, hh, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [replaceWork, hw, Tape.move]
      all_goals
        first
        | exact write_readBack _ (hw _ (by decide))
        | simp [Tape.write, hh]
    · exact transitionTape_eq_self hout
  · have hr := ht.read_ne_start (by omega)
    have allw : ∀ j, (c.work j).read ≠ .start := by
      intro j
      by_cases hj : j = 2
      · simpa only [hj] using hr
      · exact hw j hj
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, control, markerDir, hin, hr, hh, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;> simp [replaceWork, allw, Tape.move]
      all_goals
        first
        | exact write_readBack _ (allw _)
        | exact ⟨congrArg (fun t : Tape => t.head - 1) (write_readBack (c.work 2) (allw 2)),
            congrArg Tape.cells (write_readBack (c.work 2) (allw 2))⟩
    · exact transitionTape_eq_self hout

/-- Concrete phase 4 restores the temporary head without changing its cells. -/
theorem rewind_temp_run (flag : Bool) (k : ℕ) (c : Cfg 3 machine.Q)
    (hq : c.state = (4, flag, false))
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hw : ∀ j, j ≠ 2 → (c.work j).read ≠ .start)
    (ht : (c.work 2).StartInvariant) (hh : (c.work 2).head = k) :
    ∃ d, machine.reachesIn (k+1) c d ∧ d.state = (5, flag, false) ∧
      (d.work 2).head = 1 ∧ (d.work 2).cells = (c.work 2).cells ∧
      d.input = c.input ∧ d.output = c.output ∧
      ∀ j, j ≠ 2 → d.work j = c.work j := by
  induction k generalizing c with
  | zero =>
    have hs := rewind_temp_step flag c hq hin hout hw ht
    simp only [hh, ↓reduceIte] at hs
    refine ⟨_, .step hs .zero, rfl, ?_, rfl, rfl, rfl, ?_⟩
    · simp [replaceWork, Tape.move, hh]
    · intro j hj; simp [replaceWork, hj]
  | succ k ih =>
    let d := replaceWork c (4, flag, false) 2 ((c.work 2).move .left)
    have hs : machine.step c = some d := by
      simpa only [hh, Nat.succ_ne_zero, ↓reduceIte] using rewind_temp_step flag c hq hin hout hw ht
    have ht' : (d.work 2).StartInvariant := by
      simpa only [d, replaceWork, Function.update_self] using ht.move .left
    have hh' : (d.work 2).head = k := by simp [d, replaceWork, Tape.move, hh]
    have hw' : ∀ j, j ≠ 2 → (d.work j).read ≠ .start := by
      intro j hj; simpa [d, replaceWork, hj] using hw j hj
    obtain ⟨e, he, hq', hh', hc, hi, ho, hf⟩ := ih d rfl hin hout hw' ht' hh'
    refine ⟨e, .step hs he, hq', hh', ?_, hi, ho, ?_⟩
    · simpa only [d, replaceWork, Function.update_self, Tape.move] using hc
    · intro j hj; simpa [d, replaceWork, hj] using hf j hj

/-- The actual phase-3-to-phase-5 preparation, ready to consume the adder
boundary: accumulator empty and temporary rewound, with every frame retained. -/
theorem prepare_add_run (flag : Bool) (c : Cfg 3 machine.Q)
    (hq : c.state = (3, flag, false))
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hm : (c.work 0).read ≠ .start) (htRead : (c.work 2).read ≠ .start)
    (ha : (c.work 1).StartInvariant) (hb : blankAbove (c.work 1))
    (ht : (c.work 2).StartInvariant) :
    ∃ d, machine.reachesIn ((c.work 1).head + (c.work 2).head + 2) c d ∧
      d.state = (5, flag, false) ∧ d.work 1 = (Tape.init []).move .right ∧
      (d.work 2).head = 1 ∧ (d.work 2).cells = (c.work 2).cells ∧
      d.input = c.input ∧ d.output = c.output ∧ d.work 0 = c.work 0 := by
  have hw : ∀ j : Fin 3, j ≠ eraseIndex false → (c.work j).read ≠ .start := by
    intro j hj
    fin_cases j
    · exact hm
    · exact False.elim (hj rfl)
    · exact htRead
  obtain ⟨d, hd, hqd, had, hid, hod, hfd⟩ :=
    erase_run false flag (c.work 1).head c hq hin hout hw ha rfl hb
  have hd2 : d.work 2 = c.work 2 := hfd 2 (by decide)
  have hd0 : d.work 0 = c.work 0 := hfd 0 (by decide)
  have hwd : ∀ j : Fin 3, j ≠ 2 → (d.work j).read ≠ .start := by
    intro j hj
    fin_cases j
    · change (d.work 0).read ≠ .start
      rw [hd0]; exact hm
    · change (d.work (eraseIndex false)).read ≠ .start
      rw [had]
      simp
    · exact False.elim (hj rfl)
  obtain ⟨e, he, hqe, hhe, hce, hie, hoe, hfe⟩ :=
    rewind_temp_run flag (c.work 2).head d hqd
      (by simpa only [hid] using hin) (by simpa only [hod] using hout) hwd
      (by simpa only [hd2] using ht) (by rw [hd2])
  refine ⟨e, ?_, hqe, ?_, hhe, ?_, hie.trans hid, hoe.trans hod, ?_⟩
  · convert machine.reachesIn_trans hd he using 1
    omega
  · exact (hfe 1 (by decide)).trans had
  · simpa only [hd2] using hce
  · exact (hfe 0 (by decide)).trans hd0

theorem rewind_input_step (c : Cfg 3 machine.Q) (hq : c.state = (6, false, false))
    (hw : ∀ j, (c.work j).read ≠ .start) (hout : c.output.read ≠ .start)
    (ht : c.input.StartInvariant) :
    machine.step c = some { c with
      state := if c.input.head = 0 then (7, false, false) else (6, false, false),
      input := c.input.move (if c.input.head = 0 then .right else .left) } := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  by_cases hh : c.input.head = 0
  · have hr : c.input.read = .start := by
      change c.input.cells _ = .start
      rw [hh]; exact ht.1
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, control, markerDir, hr, hh, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      simp only [hw j, ↓reduceIte]
      exact writeAndMove_readBack _ (hw j) .stay
    · exact transitionTape_eq_self hout
  · have hr := ht.read_ne_start (by omega)
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, control, markerDir, hr, hh, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      simp only [hw j, ↓reduceIte]
      exact writeAndMove_readBack _ (hw j) .stay
    · exact transitionTape_eq_self hout

/-- Actual phase 6: restore the input head in h+1 steps, retaining every
work tape and all input cells for the following temporary-erasure phase. -/
theorem rewind_input_run (k : ℕ) (c : Cfg 3 machine.Q) (hq : c.state = (6, false, false))
    (hw : ∀ j, (c.work j).read ≠ .start) (hout : c.output.read ≠ .start)
    (ht : c.input.StartInvariant) (hh : c.input.head = k) :
    ∃ d, machine.reachesIn (k+1) c d ∧ d.state = (7, false, false) ∧
      d.input.head = 1 ∧ d.input.cells = c.input.cells ∧ d.work = c.work ∧ d.output = c.output := by
  induction k generalizing c with
  | zero =>
    have hs := rewind_input_step c hq hw hout ht
    simp only [hh, ↓reduceIte] at hs
    refine ⟨_, .step hs .zero, rfl, ?_, rfl, rfl, rfl⟩
    simp [Tape.move, hh]
  | succ k ih =>
    let d : Cfg 3 machine.Q := { c with input := c.input.move .left }
    have hs : machine.step c = some d := by
      simpa only [d, hh, Nat.succ_ne_zero, ↓reduceIte, hq] using rewind_input_step c hq hw hout ht
    have hdhead : d.input.head = k := by simp [d, Tape.move, hh]
    obtain ⟨e, he, hqe, hhead, hcells, hwork, ho⟩ := ih d hq hw hout (ht.move .left) hdhead
    exact ⟨e, .step hs he, hqe, hhead, hcells, hwork, ho⟩

theorem rewind_acc_step (c : Cfg 3 machine.Q) (hq : c.state = (8, false, false))
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hm : (c.work 0).read ≠ .start) (hw : (c.work 2).read ≠ .start)
    (ht : (c.work 1).StartInvariant) :
    machine.step c = some { c with
      state := if (c.work 1).head = 0 then (1, false, false) else (8, false, false),
      work := ![(c.work 0).move (if (c.work 1).head = 0 then .left else .stay),
        (c.work 1).move (if (c.work 1).head = 0 then .right else .left), c.work 2] } := by
  have hn : c.state ≠ machine.qhalt := by simp [hq, machine]
  by_cases hh : (c.work 1).head = 0
  · have hr : (c.work 1).read = .start := by
      change (c.work 1).cells _ = .start
      rw [hh]; exact ht.1
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, control, markerDir, hin, hr, hh, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j
      · change (c.work 0).writeAndMove (readBackWrite (c.work 0).read).toΓ
          (if (c.work 0).read = .start then .right else .left) = (c.work 0).move .left
        rw [ite_eq_right hm]
        exact writeAndMove_readBack _ hm .left
      · dsimp only
        simp [hr, Tape.writeAndMove, Tape.write, hh]
      · change (c.work 2).writeAndMove (readBackWrite (c.work 2).read).toΓ
          (if (c.work 2).read = .start then .right else .stay) = c.work 2
        rw [ite_eq_right hw]
        exact writeAndMove_readBack _ hw .stay
    · exact transitionTape_eq_self hout
  · have hr := ht.read_ne_start (by omega)
    simp only [TM.step, hn, ↓reduceIte]
    simp only [machine, hq, control, markerDir, hin, hr, hh, ↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j
      · change (c.work 0).writeAndMove (readBackWrite (c.work 0).read).toΓ
          (if (c.work 0).read = .start then .right else .stay) = (c.work 0).move .stay
        rw [ite_eq_right hm]
        exact writeAndMove_readBack _ hm .stay
      · change (c.work 1).writeAndMove (readBackWrite (c.work 1).read).toΓ
          (if (c.work 1).read = .start then .right else .left) = (c.work 1).move .left
        rw [ite_eq_right hr]
        exact writeAndMove_readBack _ hr .left
      · change (c.work 2).writeAndMove (readBackWrite (c.work 2).read).toΓ
          (if (c.work 2).read = .start then .right else .stay) = c.work 2
        rw [ite_eq_right hw]
        exact writeAndMove_readBack _ hw .stay
    · exact transitionTape_eq_self hout

/-- Phase 8 restores the accumulator and decrements the multiplier exactly once.
The multiplier is allowed to arrive at its marker, ready for the loop's halt test. -/
theorem rewind_acc_run (k : ℕ) (c : Cfg 3 machine.Q) (hq : c.state = (8, false, false))
    (hin : c.input.read ≠ .start) (hout : c.output.read ≠ .start)
    (hm : (c.work 0).read ≠ .start) (hw : (c.work 2).read ≠ .start)
    (ht : (c.work 1).StartInvariant) (hh : (c.work 1).head = k) :
    ∃ d, machine.reachesIn (k+1) c d ∧ d.state = (1, false, false) ∧
      (d.work 1).head = 1 ∧ (d.work 1).cells = (c.work 1).cells ∧
      d.work 0 = (c.work 0).move .left ∧ d.work 2 = c.work 2 ∧
      d.input = c.input ∧ d.output = c.output := by
  induction k generalizing c with
  | zero =>
    have hs := rewind_acc_step c hq hin hout hm hw ht
    simp only [hh, ↓reduceIte] at hs
    refine ⟨_, .step hs .zero, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
    simp [Tape.move, hh]
  | succ k ih =>
    let d : Cfg 3 machine.Q := { c with
      work := ![c.work 0, (c.work 1).move .left, c.work 2] }
    have hs : machine.step c = some d := by
      simpa only [d, hh, Nat.succ_ne_zero, ↓reduceIte, hq, Tape.move] using
        rewind_acc_step c hq hin hout hm hw ht
    have hdhead : (d.work 1).head = k := by simp [d, Tape.move, hh]
    obtain ⟨e, he, hqe, hhead, hcells, hm', hw', hi, ho⟩ :=
      ih d hq hin hout hm hw (ht.move .left) hdhead
    exact ⟨e, .step hs he, hqe, hhead, hcells, hm', hw', hi, ho⟩

end UnconstrainedPACDetection.VerifierProductMachine

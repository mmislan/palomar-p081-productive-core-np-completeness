module

public import proofs.Complexitylib.Models.TuringMachine.Lift
public import proofs.Complexitylib.Models.TuringMachine.Internal
public import Mathlib.Data.Fintype.Option

@[expose] public section

namespace IrrRAFEnumeration.DeadlineMachine
open Complexity Complexity.TM

variable {n : Nat}

/-- A terminal transition records success on the clock tape and preserves all
simulated tape cells. Heads at the left marker take their mandatory bounce. -/
def finishAction (tm : TM n) (success : Bool) (i : Γ) (w : Fin (n+1) → Γ) (o : Γ) :
    Option tm.Q × (Fin (n+1) → Γw) × Γw × Dir3 × (Fin (n+1) → Dir3) × Dir3 :=
  (none, fun j => if j.val < n then readBackWrite (w j) else Γw.ofBool success,
    readBackWrite o, idleDir i, fun j => idleDir (w j), idleDir o)

/-- One original transition per unary clock mark; original halting takes
precedence over an exhausted clock, so halting exactly at the deadline wins.
The clock is a prepared extra work tape, not an uncharged integer oracle. -/
def clockTM (tm : TM n) : TM (n+1) where
  Q := Option tm.Q
  qstart := some tm.qstart
  qhalt := none
  δ := fun state i w o => match state with
    | none => finishAction tm false i w o
    | some q =>
      if q = tm.qhalt then finishAction tm true i w o
      else if w (Fin.last n) = Γ.one then
        let r := tm.δ q i (fun j => w j.castSucc) o
        (some r.1,
          fun j => if h : j.val < n then r.2.1 ⟨j.val,h⟩ else readBackWrite (w j),
          r.2.2.1, r.2.2.2.1,
          fun j => if h : j.val < n then r.2.2.2.2.1 ⟨j.val,h⟩ else .right,
          r.2.2.2.2.2)
      else finishAction tm false i w o
  δ_right_of_start := by
    intro state i w o
    cases state with
    | none => exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | some q =>
      dsimp only
      split
      · exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
      · split
        · obtain ⟨hi,hw,ho⟩ := tm.δ_right_of_start q i (fun j => w j.castSucc) o
          refine ⟨hi,?_,ho⟩
          intro j hj
          dsimp only
          split
          · next h => exact hw ⟨j.val,h⟩ hj
          · rfl
        · exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,
            idleDir_right_of_start⟩

def clockCfg (tm : TM n) (c : Cfg n tm.Q) (clock : Tape) :
    Cfg (n+1) (clockTM tm).Q where
  state := some c.state
  input := c.input
  work j := if h : j.val < n then c.work ⟨j.val,h⟩ else clock
  output := c.output

@[simp] theorem clockCfg_work_old (tm : TM n) (c : Cfg n tm.Q) (clock : Tape)
    (j : Fin n) : (clockCfg tm c clock).work j.castSucc = c.work j := by
  simp [clockCfg]

@[simp] theorem clockCfg_work_last (tm : TM n) (c : Cfg n tm.Q) (clock : Tape) :
    (clockCfg tm c clock).work (Fin.last n) = clock := by
  simp [clockCfg]

theorem clock_step (tm : TM n) {c c' : Cfg n tm.Q} (clock : Tape)
    (hs : tm.step c = some c') (hc : clock.read = Γ.one) :
    (clockTM tm).step (clockCfg tm c clock) =
      some (clockCfg tm c' (clock.move .right)) := by
  have hn := TM.state_ne_qhalt_of_step hs
  simp only [TM.step, hn, ↓reduceIte, Option.some.injEq] at hs
  rw [← hs]
  simp only [TM.step, clockCfg, clockTM, Option.some_ne_none, ↓reduceIte,
    Option.some.injEq, hn, Fin.val_last, Nat.lt_irrefl, ↓reduceDIte,
    Fin.val_castSucc, Fin.isLt]
  simp only [hc, ↓reduceIte]
  congr 1
  funext j
  by_cases hj : j.val < n
  · simp [hj]
  · simp only [hj, ↓reduceDIte]
    exact writeAndMove_readBack clock (by rw [hc]; decide) .right

def clockTape (budget elapsed : Nat) : Tape where
  head := elapsed+1
  cells j := if j = 0 then .start else if j ≤ budget then .one else .blank

theorem clockTape_read (budget elapsed : Nat) :
    (clockTape budget elapsed).read = if elapsed < budget then Γ.one else Γ.blank := by
  simp only [Tape.read,clockTape,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
    ↓reduceIte]
  split <;> split <;> first | rfl | omega

theorem clockTape_move (budget elapsed : Nat) :
    (clockTape budget elapsed).move .right = clockTape budget (elapsed+1) := rfl

def finishCfg (tm : TM n) (success : Bool) (c : Cfg n tm.Q) (clock : Tape) :
    Cfg (n+1) (clockTM tm).Q where
  state := none
  input := c.input.move (idleDir c.input.read)
  work j := if h : j.val < n then
      (c.work ⟨j.val,h⟩).writeAndMove (readBackWrite (c.work ⟨j.val,h⟩).read)
        (idleDir (c.work ⟨j.val,h⟩).read)
    else clock.writeAndMove (Γw.ofBool success) (idleDir clock.read)
  output := c.output.writeAndMove (readBackWrite c.output.read) (idleDir c.output.read)

theorem clock_finish_halted (tm : TM n) (c : Cfg n tm.Q) (clock : Tape)
    (hh : c.state = tm.qhalt) :
    (clockTM tm).step (clockCfg tm c clock) = some (finishCfg tm true c clock) := by
  simp only [TM.step,clockCfg,clockTM,Option.some_ne_none,↓reduceIte,hh,
    finishAction,Option.some.injEq,finishCfg]
  congr 1
  funext j
  by_cases hj : j.val < n <;> simp [hj]

theorem clock_finish_timeout (tm : TM n) (c : Cfg n tm.Q) (clock : Tape)
    (hh : c.state ≠ tm.qhalt) (hc : clock.read ≠ Γ.one) :
    (clockTM tm).step (clockCfg tm c clock) = some (finishCfg tm false c clock) := by
  simp only [TM.step,clockCfg,clockTM,Option.some_ne_none,↓reduceIte,hh,
    Fin.val_last,Nat.lt_irrefl,↓reduceDIte,hc,finishAction,Option.some.injEq,finishCfg]
  congr 1
  funext j
  by_cases hj : j.val < n <;> simp [hj]

theorem finishCfg_flag (tm : TM n) (success : Bool) (c : Cfg n tm.Q)
    (budget elapsed : Nat) :
    ((finishCfg tm success c (clockTape budget elapsed)).work (Fin.last n)).read =
      Γ.ofBool success := by
  have hn : (clockTape budget elapsed).read ≠ Γ.start := by
    rw [clockTape_read]
    split <;> decide
  simp only [finishCfg,Fin.val_last,Nat.lt_irrefl,↓reduceDIte]
  rw [idleDir,ite_eq_right hn]
  cases success <;> simp [Tape.writeAndMove,Tape.move,Tape.read,Tape.write,clockTape,
    Γw.ofBool,Γ.ofBool]

/-- The real clocked machine exactly follows every source prefix that fits
inside the prepared clock. No output observation is made during the prefix. -/
theorem clock_simulates (tm : TM n) {t : Nat} {c c' : Cfg n tm.Q}
    (hr : tm.reachesIn t c c') (budget elapsed : Nat) (ht : elapsed+t ≤ budget) :
    (clockTM tm).reachesIn t (clockCfg tm c (clockTape budget elapsed))
      (clockCfg tm c' (clockTape budget (elapsed+t))) := by
  induction hr generalizing elapsed with
  | zero => simpa using (TM.reachesIn.zero (tm := clockTM tm))
  | @step c cm t c' hs hr ih =>
    have hc : (clockTape budget elapsed).read = Γ.one := by
      rw [clockTape_read,ite_eq_left (by omega)]
    have hstep := clock_step tm (clockTape budget elapsed) hs hc
    rw [clockTape_move] at hstep
    have htail := ih (elapsed+1) (by omega)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (TM.reachesIn.step hstep htail)

/-- Inclusive endpoint theorem for an actual bounded machine: a source
halting after t ≤ T transitions is reported successful after t+1 transitions. -/
theorem clock_success_run (tm : TM n) {t : Nat} {c c' : Cfg n tm.Q}
    (hr : tm.reachesIn t c c') (hh : c'.state = tm.qhalt) (budget : Nat)
    (ht : t ≤ budget) :
    (clockTM tm).reachesIn (t+1) (clockCfg tm c (clockTape budget 0))
      (finishCfg tm true c' (clockTape budget t)) := by
  have hp := clock_simulates tm hr budget 0 (by simpa using ht)
  simp only [Nat.zero_add] at hp
  have hs := clock_finish_halted tm c' (clockTape budget t) hh
  exact TM.reachesIn_trans (clockTM tm) hp (TM.reachesIn.step hs TM.reachesIn.zero)

theorem clock_timeout_run (tm : TM n) {c c' : Cfg n tm.Q} (budget : Nat)
    (hr : tm.reachesIn budget c c') (hh : c'.state ≠ tm.qhalt) :
    (clockTM tm).reachesIn (budget+1) (clockCfg tm c (clockTape budget 0))
      (finishCfg tm false c' (clockTape budget budget)) := by
  have hp := clock_simulates tm hr budget 0 (by omega)
  simp only [Nat.zero_add] at hp
  have hc : (clockTape budget budget).read ≠ Γ.one := by simp [clockTape_read]
  exact TM.reachesIn_trans (clockTM tm) hp
    (TM.reachesIn.step (clock_finish_timeout tm c' _ hh hc) TM.reachesIn.zero)

/-- A deterministic machine has either halted or made exactly the requested
number of transitions. This lemma does not assume that it eventually halts. -/
theorem prefix_exists (tm : TM n) (budget : Nat) (c : Cfg n tm.Q) :
    ∃ c' t, t ≤ budget ∧ tm.reachesIn t c c' ∧
      (c'.state = tm.qhalt ∨ t = budget) := by
  induction budget generalizing c with
  | zero => exact ⟨c,0,le_refl _,TM.reachesIn.zero,Or.inr rfl⟩
  | succ budget ih =>
    by_cases hh : c.state = tm.qhalt
    · exact ⟨c,0,Nat.zero_le _,TM.reachesIn.zero,Or.inl hh⟩
    · cases hs : tm.step c with
      | none => simp [TM.step,hh] at hs
      | some cm =>
        obtain ⟨c',t,ht,hr,he⟩ := ih cm
        refine ⟨c',t+1,by omega,TM.reachesIn.step hs hr,?_⟩
        exact he.imp id (fun h => by omega)

/-- Universal bounded-run contract for the actual clocked TM. The extra step
writes a success flag on the clock tape; it never examines unfinished output.
Clock construction is an explicit remaining obligation of initialization. -/
theorem clock_bounded_correct (tm : TM n) (budget : Nat) (c : Cfg n tm.Q) :
    ∃ c' t success,
      t ≤ budget ∧ tm.reachesIn t c c' ∧
      (success = true ↔ ∃ d s, s ≤ budget ∧ tm.reachesIn s c d ∧ d.state = tm.qhalt) ∧
      (clockTM tm).reachesIn (t+1) (clockCfg tm c (clockTape budget 0))
        (finishCfg tm success c' (clockTape budget t)) ∧
      (clockTM tm).halted (finishCfg tm success c' (clockTape budget t)) ∧
      ((finishCfg tm success c' (clockTape budget t)).work (Fin.last n)).read =
        Γ.ofBool success := by
  obtain ⟨c',t,ht,hr,he⟩ := prefix_exists tm budget c
  by_cases hh : c'.state = tm.qhalt
  · refine ⟨c',t,true,ht,hr,?_,clock_success_run tm hr hh budget ht,rfl,
      finishCfg_flag tm true c' budget t⟩
    exact iff_of_true rfl ⟨c',t,ht,hr,hh⟩
  · have heq : t = budget := he.resolve_left hh
    subst t
    refine ⟨c',budget,false,le_refl _,hr,?_,clock_timeout_run tm budget hr hh,rfl,
      finishCfg_flag tm false c' budget budget⟩
    constructor
    · intro hf; cases hf
    · rintro ⟨d,s,hs,hreach,hhalt⟩
      have hle := tm.reachesIn_le_halt hr hreach hhalt
      have hst : s = budget := by omega
      subst s
      have hd := TM.reachesIn_right_unique hr hreach
      exact False.elim (hh (hd ▸ hhalt))

theorem finish_output_preserved (tm : TM n) (success : Bool) (c : Cfg n tm.Q)
    (clock : Tape) (hinv : c.output.StartInvariant) :
    (finishCfg tm success c clock).output.cells = c.output.cells := by
  change (c.output.writeAndMove (readBackWrite c.output.read) _).cells = _
  simp only [Tape.writeAndMove,Tape.move_cells]
  by_cases hz : c.output.head = 0
  · simp [Tape.write,hz]
  · rw [write_readBack c.output (hinv.read_ne_start (by omega))]

end IrrRAFEnumeration.DeadlineMachine

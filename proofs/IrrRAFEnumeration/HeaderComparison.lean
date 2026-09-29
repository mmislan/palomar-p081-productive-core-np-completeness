module

public import proofs.IrrRAFEnumeration.DeadlineMachine
public import proofs.Complexitylib.Models.TuringMachine.Registers
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace IrrRAFEnumeration.HeaderComparison
open Complexity Complexity.TM

/-- Compare a completed unary output header with work register 0. Register 1
receives the verdict. The output tape is preserved. States 0/1/2 mean rewind,
compare, and halt. The bound depends on the supplied count, not actual output. -/
def headerTM : TM 2 where
  Q := Fin 3
  qstart := 0
  qhalt := 2
  δ := fun s i w o =>
    if s = 0 then
      (if o = Γ.start then 1 else 0,
        fun j => readBackWrite (w j),readBackWrite o,idleDir i,
        fun j => idleDir (w j),if o = Γ.start then .right else .left)
    else if o = Γ.one ∧ w 0 = Γ.one then
      (1,fun j => readBackWrite (w j),readBackWrite o,idleDir i,
        fun j => if j = 0 then .right else idleDir (w j),.right)
    else
      (2,fun j => if j = 1 then Γw.ofBool (decide (o = Γ.zero ∧ w 0 = Γ.blank))
          else readBackWrite (w j),readBackWrite o,idleDir i,
        fun j => idleDir (w j),idleDir o)
  δ_right_of_start := by
    intro s i w o
    by_cases hs : s = 0
    · simp only [ite_eq_left hs]
      refine ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,?_⟩
      intro h; simp [h]
    · simp only [ite_eq_right hs]
      by_cases hm : o = Γ.one ∧ w 0 = Γ.one
      · simp only [ite_eq_left hm]
        refine ⟨idleDir_right_of_start,?_,fun _ => trivial⟩
        intro j hj
        by_cases hj0 : j = 0
        · simp [hj0]
        · simp only [ite_eq_right hj0]
          exact idleDir_right_of_start hj
      · simp only [ite_eq_right hm]
        exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩

def config (state : Fin 3) (inp expected flag out : Tape) : Cfg 2 headerTM.Q where
  state := state
  input := inp
  work j := if j = 0 then expected else flag
  output := out

theorem scan_one_step (inp expected flag out : Tape)
    (hi : Parked inp) (hf : Parked flag)
    (he : expected.read = Γ.one) (ho : out.read = Γ.one) :
    headerTM.step (config 1 inp expected flag out) =
      some (config 1 inp (expected.move .right) flag (out.move .right)) := by
  have hen : expected.read ≠ Γ.start := by rw [he]; decide
  have hon : out.read ≠ Γ.start := by rw [ho]; decide
  simp only [TM.step,headerTM,config,show (1 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide,↓reduceIte,he,ho,and_self,
    Option.some.injEq]
  rw [hi.move_idle]
  congr 1
  · funext j
    fin_cases j
    · simpa [he] using writeAndMove_readBack expected hen .right
    · simpa using hf.writeAndMove_readBack_idle
  · simpa [ho] using writeAndMove_readBack out hon .right

theorem scan_stop_step (inp expected flag out : Tape)
    (hi : Parked inp) (he : Parked expected) (ho : Parked out)
    (hf : Parked flag) (hn : ¬ (out.read = Γ.one ∧ expected.read = Γ.one)) :
    headerTM.step (config 1 inp expected flag out) =
      some (config 2 inp expected
        (flag.write (Γw.ofBool (decide (out.read = Γ.zero ∧ expected.read = Γ.blank)))) out) := by
  simp only [TM.step,headerTM,config,show (1 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide,↓reduceIte,hn,Option.some.injEq]
  rw [hi.move_idle]
  congr 1
  · funext j
    fin_cases j
    · simpa using he.writeAndMove_readBack_idle
    · change (flag.write (Γw.ofBool (decide (out.read = Γ.zero ∧ expected.read = Γ.blank)))).move
        (idleDir flag.read) = _
      rw [idleDir,ite_eq_right hf.read_ne_start]
      rfl
  · exact ho.writeAndMove_readBack_idle

def UnaryPrefix (t : Tape) (count : Nat) (terminal : Γ) : Prop :=
  (∀ j < count, t.cells (t.head+j) = Γ.one) ∧ t.cells (t.head+count) = terminal

theorem prefix_zero {t : Tape} {terminal : Γ} (h : UnaryPrefix t 0 terminal) :
    t.read = terminal := by simpa [Tape.read] using h.2

theorem prefix_succ {t : Tape} {count : Nat} {terminal : Γ}
    (h : UnaryPrefix t (count+1) terminal) : t.read = Γ.one := by
  simpa [Tape.read] using h.1 0 (by omega)

theorem prefix_tail {t : Tape} {count : Nat} {terminal : Γ}
    (h : UnaryPrefix t (count+1) terminal) :
    UnaryPrefix (t.move .right) count terminal := by
  constructor
  · intro j hj
    simpa [Tape.move,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.1 (j+1) (by omega)
  · simpa [Tape.move,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2

def advance (t : Tape) (steps : Nat) : Tape := {t with head := t.head+steps}

@[simp] theorem advance_zero (t : Tape) : advance t 0 = t := by cases t; rfl

theorem advance_right (t : Tape) (steps : Nat) :
    advance (t.move .right) steps = advance t (steps+1) := by
  simp [advance,Tape.move,Nat.add_comm,Nat.add_left_comm]

theorem parked_right {t : Tape} (h : Parked t) : Parked (t.move .right) :=
  ⟨by simp [Tape.move], h.2⟩

/-- Exactly min(actual,supplied)+1 transitions compare a completed count
header. The potentially enormous actual count is never scanned in full. -/
theorem scan_header_run (actual supplied : Nat) (inp expected flag out : Tape)
    (hi : Parked inp) (he : Parked expected) (hf : Parked flag) (ho : Parked out)
    (hE : UnaryPrefix expected supplied Γ.blank) (hO : UnaryPrefix out actual Γ.zero) :
    headerTM.reachesIn (min actual supplied+1) (config 1 inp expected flag out)
      (config 2 inp (advance expected (min actual supplied))
        (flag.write (Γw.ofBool (decide (actual = supplied))))
        (advance out (min actual supplied))) := by
  induction actual generalizing supplied expected out with
  | zero =>
    have hout := prefix_zero hO
    cases supplied with
    | zero =>
      have hexpected := prefix_zero hE
      have hs := scan_stop_step inp expected flag out hi he ho hf
        (by simp [hout])
      simpa [hout,hexpected] using (TM.reachesIn.step hs TM.reachesIn.zero)
    | succ supplied =>
      have hexpected := prefix_succ hE
      have hs := scan_stop_step inp expected flag out hi he ho hf
        (by simp [hout])
      simpa [hout,hexpected] using (TM.reachesIn.step hs TM.reachesIn.zero)
  | succ actual ih =>
    have hout := prefix_succ hO
    cases supplied with
    | zero =>
      have hexpected := prefix_zero hE
      have hs := scan_stop_step inp expected flag out hi he ho hf
        (by simp [hexpected])
      simpa [hout,hexpected] using (TM.reachesIn.step hs TM.reachesIn.zero)
    | succ supplied =>
      have hs := scan_one_step inp expected flag out hi hf (prefix_succ hE) hout
      have hr := ih supplied (expected.move .right) (out.move .right)
        (parked_right he) (parked_right ho) (prefix_tail hE) (prefix_tail hO)
      simpa [advance_right,Nat.succ_eq_add_one] using (TM.reachesIn.step hs hr)

theorem verdict_read (flag : Tape) (hf : Parked flag) (answer : Bool) :
    (flag.write (Γw.ofBool answer)).read = Γ.ofBool answer := by
  have hh : flag.head ≠ 0 := by have := hf.1; omega
  cases answer <;> simp [Tape.read,Tape.write,hh,Γw.ofBool,Γ.ofBool]

def parkOutput (out : Tape) : Tape := {out with head := 1}

theorem rewind_step_left (inp expected flag out : Tape)
    (hi : Parked inp) (he : Parked expected) (hf : Parked flag) (ho : Parked out) :
    headerTM.step (config 0 inp expected flag out) =
      some (config 0 inp expected flag (out.move .left)) := by
  simp only [TM.step,headerTM,config,show (0 : Fin 3) ≠ 2 by decide,
    ↓reduceIte,ite_eq_right ho.read_ne_start,Option.some.injEq]
  rw [hi.move_idle]
  congr 1
  · funext j
    fin_cases j
    · simpa using he.writeAndMove_readBack_idle
    · simpa using hf.writeAndMove_readBack_idle
  · exact writeAndMove_readBack out ho.read_ne_start .left

theorem rewind_step_zero (inp expected flag out : Tape)
    (hi : Parked inp) (he : Parked expected) (hf : Parked flag)
    (ho : out.StartInvariant) (hp : out.head = 0) :
    headerTM.step (config 0 inp expected flag out) =
      some (config 1 inp expected flag (parkOutput out)) := by
  have hread : out.read = Γ.start := by simpa [Tape.read,hp] using ho.1
  simp only [TM.step,headerTM,config,show (0 : Fin 3) ≠ 2 by decide,
    ↓reduceIte,hread,Option.some.injEq]
  rw [hi.move_idle]
  congr 1
  · funext j
    fin_cases j
    · simpa using he.writeAndMove_readBack_idle
    · simpa using hf.writeAndMove_readBack_idle
  · simp [Tape.writeAndMove,Tape.write,hp,Tape.move,parkOutput]

theorem rewind_run (p : Nat) (inp expected flag out : Tape)
    (hi : Parked inp) (he : Parked expected) (hf : Parked flag)
    (ho : out.StartInvariant) (hp : out.head = p) :
    headerTM.reachesIn (p+1) (config 0 inp expected flag out)
      (config 1 inp expected flag (parkOutput out)) := by
  induction p generalizing out with
  | zero =>
    exact TM.reachesIn.step (rewind_step_zero inp expected flag out hi he hf ho hp)
      TM.reachesIn.zero
  | succ p ih =>
    have hpark : Parked out := ⟨by omega,ho.2⟩
    have hs := rewind_step_left inp expected flag out hi he hf hpark
    have htail := ih (out.move .left) ⟨ho.1,ho.2⟩ (by simp [Tape.move,hp])
    simpa [parkOutput,Tape.move] using TM.reachesIn.step hs htail

/-- Complete rewind-and-compare routine. Its exact runtime is bounded by
the initial output-head position plus the supplied count plus two. The final
verdict lives on the flag tape, and every source output cell is preserved. -/
theorem header_comparison_correct (actual supplied : Nat) (inp expected flag out : Tape)
    (hi : Parked inp) (he : Parked expected) (hf : Parked flag)
    (ho : out.StartInvariant) (hE : UnaryPrefix expected supplied Γ.blank)
    (hO : UnaryPrefix (parkOutput out) actual Γ.zero) :
    ∃ final t,
      t ≤ out.head+supplied+2 ∧
      headerTM.reachesIn t (config 0 inp expected flag out) final ∧
      headerTM.halted final ∧
      (final.work 1).read = Γ.ofBool (decide (actual = supplied)) ∧
      final.output.cells = out.cells := by
  have hrewind := rewind_run out.head inp expected flag out hi he hf ho rfl
  have hpark : Parked (parkOutput out) := ⟨by simp [parkOutput],ho.2⟩
  have hscan := scan_header_run actual supplied inp expected flag (parkOutput out)
    hi he hf hpark hE hO
  refine ⟨_,(out.head+1)+(min actual supplied+1),?_,
    TM.reachesIn_trans headerTM hrewind hscan,rfl,?_,rfl⟩
  · have := min_le_right actual supplied
    omega
  · simpa [config] using verdict_read flag hf (decide (actual = supplied))

end IrrRAFEnumeration.HeaderComparison

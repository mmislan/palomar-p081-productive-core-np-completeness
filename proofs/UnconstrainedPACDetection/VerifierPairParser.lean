module

public import proofs.Complexitylib.Models.TuringMachine.Registers.Emit
public import proofs.Complexitylib.Models.TuringMachine.Tape.Encoding
public import proofs.Complexitylib.Encoding.Pairing
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace UnconstrainedPACDetection.VerifierPairParser
open Complexity Complexity.TM

/-- Scan doubled source bits, then copy the witness verbatim. No numerical
header or relative witness-length restriction controls this parser. -/
abbrev Phase := Fin 5

def boolWrite (b : Bool) : Γw := if b then .one else .zero

def rule (q : Phase) (i : Γ) : Phase × Option (Fin 2 × Bool) × Option Bool × Bool :=
  match q.val, i with
  | 0, .zero => (1, none, none, true)
  | 0, .one => (2, none, none, true)
  | 1, .zero => (0, some (0,false), none, true)
  | 1, .one => (3, none, none, true)
  | 2, .one => (0, some (0,true), none, true)
  | 3, .zero => (3, some (1,false), none, true)
  | 3, .one => (3, some (1,true), none, true)
  | 3, .blank => (4, none, some true, false)
  | _, _ => (4, none, some false, false)

def machine : TM 2 where
  Q := Phase
  qstart := 0
  qhalt := 4
  δ := fun q i w o =>
    let r := rule q i
    (r.1,
      fun j => match r.2.1 with
        | some (k,b) => if j = k then boolWrite b else readBackWrite (w j)
        | none => readBackWrite (w j),
      match r.2.2.1 with | some b => boolWrite b | none => readBackWrite o,
      if r.2.2.2 then .right else idleDir i,
      fun j => match r.2.1 with
        | some (k,_) => if j = k then .right else idleDir (w j)
        | none => idleDir (w j),
      match r.2.2.1 with | some _ => .right | none => idleDir o)
  δ_right_of_start := by
    intro q i w o
    dsimp only
    refine ⟨?_,?_,?_⟩
    · split <;> simp_all [idleDir]
    · intro j hj
      split
      · split <;> simp_all [idleDir]
      · exact idleDir_right_of_start hj
    · split
      · exact fun _ => rfl
      · exact idleDir_right_of_start

def config (q : Phase) (inp a b out : Tape) : Cfg 2 machine.Q :=
  ⟨q,inp,(fun j => if j = 0 then a else b),out⟩

theorem step_rule (q : Phase) (hq : q ≠ 4) (inp a b out : Tape)
    (ha : Parked a) (hb : Parked b) (ho : Parked out)
    (next : Phase) (payload : Option (Fin 2 × Bool)) (verdict : Option Bool) (advance : Bool)
    (hr : rule q inp.read = (next,payload,verdict,advance)) :
    machine.step (config q inp a b out) = some
      (config next (inp.move (if advance then .right else idleDir inp.read))
        (match payload with
          | some (0,v) => a.writeAndMove (Γ.ofBool v) .right
          | _ => a)
        (match payload with
          | some (1,v) => b.writeAndMove (Γ.ofBool v) .right
          | _ => b)
        (match verdict with
          | some v => out.writeAndMove (Γ.ofBool v) .right
          | none => out)) := by
  simp only [TM.step,config,machine,hq,↓reduceIte,hr]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    fin_cases j <;> cases payload with
    | none => first | exact ha.writeAndMove_readBack_idle | exact hb.writeAndMove_readBack_idle
    | some kv =>
      obtain ⟨k,v⟩ := kv
      fin_cases k <;> cases v
      all_goals first | rfl | exact ha.writeAndMove_readBack_idle | exact hb.writeAndMove_readBack_idle
  · cases verdict with
    | none => exact ho.writeAndMove_readBack_idle
    | some v => cases v <;> rfl

theorem copy_tail (ys : List Bool) : ∀ (inp a b out : Tape) (acc : List Bool),
    inp.HasBinarySuffix ys → Parked a → OutAcc acc b → OutAcc [] out →
    ∃ d, machine.reachesIn (ys.length+1) (config 3 inp a b out) d ∧
      machine.halted d ∧ d.work 0 = a ∧ OutAcc (acc ++ ys) (d.work 1) ∧
      OutAcc [true] d.output := by
  induction ys with
  | nil =>
    intro inp a b out acc hi ha hb ho
    have hs := step_rule 3 (by decide) inp a b out ha hb.parked ho.parked
      4 none (some true) false (by rw [hi.read_nil]; rfl)
    simp only [Bool.false_eq_true,↓reduceIte] at hs
    have hm : inp.move (idleDir inp.read) = inp := by
      simp [idleDir,hi.read_ne_start,Tape.move]
    rw [hm] at hs
    refine ⟨_,.step hs .zero,rfl,rfl,?_,?_⟩
    · simpa [config] using hb
    · exact outAcc_append_bit ho true
  | cons bit ys ih =>
    intro inp a b out acc hi ha hb ho
    have hs := step_rule 3 (by decide) inp a b out ha hb.parked ho.parked
      3 (some (1,bit)) none true (by rw [hi.read_cons]; cases bit <;> rfl)
    obtain ⟨d,hd,hh,ha',hb',ho'⟩ := ih (inp.move .right) a
      (b.writeAndMove (Γ.ofBool bit) .right) out (acc ++ [bit])
      hi.move_right_cons ha (outAcc_append_bit hb bit) ho
    refine ⟨d,?_,hh,ha',?_,ho'⟩
    · exact .step hs hd
    · simpa only [List.append_assoc,List.singleton_append] using hb'

theorem token (bit : Bool) (rest : List Bool) (inp a b out : Tape)
    (hi : inp.HasBinarySuffix (bit :: bit :: rest))
    (ha : Parked a) (hb : Parked b) (ho : Parked out) :
    machine.reachesIn 2 (config 0 inp a b out)
      (config 0 ((inp.move .right).move .right)
        (a.writeAndMove (Γ.ofBool bit) .right) b out) := by
  have h1 := step_rule 0 (by decide) inp a b out ha hb ho
    (if bit then 2 else 1) none none true
    (by rw [hi.read_cons]; cases bit <;> rfl)
  have h2 := step_rule (if bit then 2 else 1) (by cases bit <;> decide)
    (inp.move .right) a b out ha hb ho 0 (some (0,bit)) none true
    (by rw [hi.move_right_cons.read_cons]; cases bit <;> rfl)
  exact .step h1 (.step h2 .zero)

theorem separator (rest : List Bool) (inp a b out : Tape)
    (hi : inp.HasBinarySuffix (false :: true :: rest))
    (ha : Parked a) (hb : Parked b) (ho : Parked out) :
    machine.reachesIn 2 (config 0 inp a b out)
      (config 3 ((inp.move .right).move .right) a b out) := by
  have h1 := step_rule 0 (by decide) inp a b out ha hb ho 1 none none true
    (by rw [hi.read_cons]; rfl)
  have h2 := step_rule 1 (by decide) (inp.move .right) a b out ha hb ho
    3 none none true (by rw [hi.move_right_cons.read_cons]; rfl)
  exact .step h1 (.step h2 .zero)

theorem scan_pair (xs ys : List Bool) : ∀ (inp a b out : Tape) (acc : List Bool),
    inp.HasBinarySuffix (pair xs ys) → OutAcc acc a → OutAcc [] b → OutAcc [] out →
    ∃ d, machine.reachesIn (2*xs.length+ys.length+3) (config 0 inp a b out) d ∧
      machine.halted d ∧ OutAcc (acc ++ xs) (d.work 0) ∧ OutAcc ys (d.work 1) ∧
      OutAcc [true] d.output := by
  induction xs with
  | nil =>
    intro inp a b out acc hi ha hb ho
    have hsep : inp.HasBinarySuffix (false :: true :: ys) := hi
    have hs := separator ys inp a b out hsep ha.parked hb.parked ho.parked
    obtain ⟨d,hd,hh,hda,hdb,hdo⟩ := copy_tail ys _ a b out []
      hsep.move_right_cons.move_right_cons ha.parked hb ho
    refine ⟨d,?_,hh,?_,?_,hdo⟩
    · convert machine.reachesIn_trans hs hd using 1; simp; omega
    · simpa only [hda,List.append_nil] using ha
    · simpa only [List.nil_append] using hdb
  | cons bit xs ih =>
    intro inp a b out acc hi ha hb ho
    rw [pair_cons_eq] at hi
    have hs := token bit (pair xs ys) inp a b out hi ha.parked hb.parked ho.parked
    obtain ⟨d,hd,hh,hda,hdb,hdo⟩ := ih ((inp.move .right).move .right)
      (a.writeAndMove (Γ.ofBool bit) .right) b out (acc ++ [bit])
      hi.move_right_cons.move_right_cons (outAcc_append_bit ha bit) hb ho
    refine ⟨d,?_,hh,?_,hdb,hdo⟩
    · convert machine.reachesIn_trans hs hd using 1; simp; omega
    · simpa only [List.append_assoc,List.singleton_append] using hda

end UnconstrainedPACDetection.VerifierPairParser

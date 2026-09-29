module

public import proofs.Complexitylib.Models.TuringMachine.Hoare.Defs
public import proofs.Complexitylib.Models.TuringMachine.Trace
public import proofs.Complexitylib.Models.TuringMachine.Combinators
public import proofs.Complexitylib.Models.TuringMachine.Combinators.Internal.Generic

@[expose] public section

namespace UnconstrainedPACDetection.VerifierNTMSequence
open Complexity Complexity.TM
variable {n : Nat}

/-- Sequential composition used by the concrete PAC guess-and-verify machine.
The boundary takes one charged idle transition. -/
def machine (A B : NTM n) : NTM n where
  Q := A.Q ⊕ B.Q
  qstart := .inl A.qstart
  qhalt := .inr B.qhalt
  δ := fun bit q i w o => match q with
    | .inl a =>
      if a = A.qhalt then allReadBack (.inr B.qstart) i w o
      else
        let r := A.δ bit a i w o
        (.inl r.1,r.2)
    | .inr b =>
      let r := B.δ bit b i w o
      (.inr r.1,r.2)
  δ_right_of_start := by
    intro bit q i w o
    cases q with
    | inl a =>
      dsimp only
      split
      · exact rightOfStart_allReadBack i w o
      · exact A.δ_right_of_start bit a i w o
    | inr b => exact B.δ_right_of_start bit b i w o

def left (A B : NTM n) (c : Cfg n A.Q) : Cfg n (machine A B).Q :=
  ⟨.inl c.state,c.input,c.work,c.output⟩

def right (A B : NTM n) (c : Cfg n B.Q) : Cfg n (machine A B).Q :=
  ⟨.inr c.state,c.input,c.work,c.output⟩

def boundary (B : NTM n) (inp : Tape) (work : Fin n → Tape) (out : Tape) : Cfg n B.Q :=
  ⟨B.qstart,transitionInput inp,fun j => transitionTape (work j),transitionTape out⟩

theorem left_step (A B : NTM n) (bit : Bool) (c : Cfg n A.Q) (hc : ¬A.halted c) :
    (machine A B).trace 1 (fun _ => bit) (left A B c) =
      left A B (A.trace 1 (fun _ => bit) c) := by
  change c.state ≠ A.qhalt at hc
  simp [NTM.trace,machine,left,hc]

theorem right_step (A B : NTM n) (bit : Bool) (c : Cfg n B.Q) :
    (machine A B).trace 1 (fun _ => bit) (right A B c) =
      right A B (B.trace 1 (fun _ => bit) c) := by
  by_cases hc : c.state = B.qhalt
  · simp [NTM.trace,machine,right,hc]
  · simp [NTM.trace,machine,right,hc]

theorem right_trace (A B : NTM n) (f : Nat → Bool) (T : Nat) (c : Cfg n B.Q) :
    (machine A B).trace T (fun i => f i.val) (right A B c) =
      right A B (B.trace T (fun i => f i.val) c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [(machine A B).trace_snoc,B.trace_snoc]
    change (machine A B).trace 1 (fun _ => f T)
      ((machine A B).trace T (fun i => f i.val) (right A B c)) =
      right A B (B.trace 1 (fun _ => f T) (B.trace T (fun i => f i.val) c))
    rw [ih]
    exact right_step A B (f T) _

theorem left_until (A B : NTM n) (f : Nat → Bool) (T : Nat) (c : Cfg n A.Q)
    (hfirst : ∀ s, s < T → ¬A.halted (A.trace s (fun i => f i.val) c)) :
    (machine A B).trace T (fun i => f i.val) (left A B c) =
      left A B (A.trace T (fun i => f i.val) c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [(machine A B).trace_snoc,A.trace_snoc]
    change (machine A B).trace 1 (fun _ => f T)
      ((machine A B).trace T (fun i => f i.val) (left A B c)) =
      left A B (A.trace 1 (fun _ => f T) (A.trace T (fun i => f i.val) c))
    rw [ih (fun s hs => hfirst s (by omega))]
    exact left_step A B (f T) _ (hfirst T (by omega))

theorem exit_step (A B : NTM n) (bit : Bool) (c : Cfg n A.Q) (hc : A.halted c) :
    (machine A B).trace 1 (fun _ => bit) (left A B c) =
      right A B (boundary B c.input c.work c.output) := by
  change c.state = A.qhalt at hc
  simp [NTM.trace,machine,left,right,boundary,hc,allReadBack,transitionInput,transitionTape]

/-- All-path sequential composition. The first component is spliced at its
first halt, so early stopping does not waste or misalign later choice bits. -/
theorem hoare (A B : NTM n) {P Q R : Complexity.TapePred n} {a b : Nat}
    (hA : A.HoareTime P Q a) (hB : B.HoareTime Q R b)
    (hstable : ∀ inp work out, Q inp work out →
      Q (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out)) :
    (machine A B).HoareTime P R (a+1+b) := by
  intro inp work out hpre choices
  let f : Nat → Bool := fun i => if hi : i < a+1+b then choices ⟨i,hi⟩ else false
  let c : Cfg n A.Q := ⟨A.qstart,inp,work,out⟩
  obtain ⟨t,ht,hhaltA,hQ,hfirst⟩ := hA.exists_first_halt_time_with_post hpre (fun i => f i.val)
  let d : Cfg n A.Q := A.trace t (fun i => f i.val) c
  have hd : A.halted d := hhaltA
  have hq : Q d.input d.work d.output := hQ
  have hl := left_until A B f t c (fun s hs => hfirst s hs)
  have hfun : (fun i : Fin 1 => f (t+i.val)) = (fun _ => f t) := by
    funext i
    have hz : i.val = 0 := by have := i.isLt; omega
    simp only [hz,Nat.add_zero]
  have hboundary : (machine A B).trace (t+1) (fun i => f i.val) (left A B c) =
      right A B (boundary B d.input d.work d.output) := by
    rw [(machine A B).trace_add_fun t 1 f (left A B c),hl,hfun]
    exact exit_step A B (f t) d hd
  have hfull : (machine A B).trace (t+1+b) (fun i => f i.val) (left A B c) =
      right A B (B.trace b (fun i => f (t+1+i.val)) (boundary B d.input d.work d.output)) := by
    rw [(machine A B).trace_add_fun (t+1) b f (left A B c),hboundary]
    exact right_trace A B (fun i => f (t+1+i)) b _
  have hb := hB (transitionInput d.input) (fun j => transitionTape (d.work j))
    (transitionTape d.output) (hstable _ _ _ hq) (fun i => f (t+1+i.val))
  have hhalt : (machine A B).halted
      ((machine A B).trace (t+1+b) (fun i => f i.val) (left A B c)) := by
    rw [hfull]
    exact congrArg (fun q => (Sum.inr q : A.Q ⊕ B.Q)) hb.1
  have hmono := (machine A B).trace_mono (by omega : t+1+b ≤ a+1+b)
    (choices := fun i => f i.val) (choices' := choices) (c := left A B c)
    (by intro i; have hi : i.val < a+1+b := by have := i.isLt; omega
        simp [f,hi]) hhalt
  constructor
  · change (machine A B).halted ((machine A B).trace (a+1+b) choices (left A B c))
    rw [hmono]; exact hhalt
  · change R ((machine A B).trace (a+1+b) choices (left A B c)).input
      ((machine A B).trace (a+1+b) choices (left A B c)).work
      ((machine A B).trace (a+1+b) choices (left A B c)).output
    rw [hmono,hfull]
    exact hb.2

/-- Splice specified choices at a known first halt. This supplies the
existential branch obligation separately from all-path termination. -/
theorem chosen_at (A B : NTM n) (fa fb : Nat → Bool) (t b : Nat) (c : Cfg n A.Q)
    (hfirst : ∀ s, s < t → ¬A.halted (A.trace s (fun i => fa i.val) c))
    (ha : A.halted (A.trace t (fun i => fa i.val) c)) :
    ∃ choices : Fin (t+1+b) → Bool,
      (machine A B).trace (t+1+b) choices (left A B c) =
        right A B (B.trace b (fun i => fb i.val)
          (boundary B (A.trace t (fun i => fa i.val) c).input
            (A.trace t (fun i => fa i.val) c).work
            (A.trace t (fun i => fa i.val) c).output)) := by
  let f : Nat → Bool := fun i => if i < t then fa i else fb (i-(t+1))
  have hprefix (s : Nat) (hs : s ≤ t) :
      (fun i : Fin s => f i.val) = (fun i => fa i.val) := by
    funext i
    have hi : i.val < t := by have := i.isLt; omega
    simp [f,hi]
  have hleft := left_until A B f t c (by
    intro s hs
    rw [hprefix s (by omega)]
    exact hfirst s hs)
  rw [hprefix t le_rfl] at hleft
  have hboundary : (machine A B).trace (t+1) (fun i => f i.val) (left A B c) =
      right A B (boundary B (A.trace t (fun i => fa i.val) c).input
        (A.trace t (fun i => fa i.val) c).work (A.trace t (fun i => fa i.val) c).output) := by
    rw [(machine A B).trace_add_fun t 1 f (left A B c),hprefix t le_rfl,hleft]
    have hone : (fun i : Fin 1 => f (t+i.val)) = (fun _ => f t) := by
      funext i
      have hi : i.val = 0 := by have := i.isLt; omega
      simp only [hi,Nat.add_zero]
    rw [hone]
    exact exit_step A B (f t) _ ha
  refine ⟨fun i => f i.val,?_⟩
  rw [(machine A B).trace_add_fun (t+1) b f (left A B c),hboundary]
  have htail : (fun i : Fin b => f (t+1+i.val)) = (fun i => fb i.val) := by
    funext i
    simp [f,show ¬t+1+i.val < t by omega]
  rw [htail]
  exact right_trace A B fb b _

/-- Composition of two specified halting traces, padded to the sum of their
bounds. The second trace begins on the charged boundary configuration. -/
theorem chosen (A B : NTM n) (a b : Nat) (ca : Fin a → Bool) (cb : Fin b → Bool)
    (c : Cfg n A.Q) (ha : A.halted (A.trace a ca c))
    (hb : B.halted (B.trace b cb (boundary B (A.trace a ca c).input
      (A.trace a ca c).work (A.trace a ca c).output))) :
    ∃ choices : Fin (a+1+b) → Bool,
      (machine A B).trace (a+1+b) choices (left A B c) =
        right A B (B.trace b cb (boundary B (A.trace a ca c).input
          (A.trace a ca c).work (A.trace a ca c).output)) := by
  obtain ⟨t,ht,hh,hfirst⟩ := NTM.exists_first_halt_time_of_trace_halted A a ca c ha
  let fa : Nat → Bool := fun i => if hi : i < a then ca ⟨i,hi⟩ else false
  let fb : Nat → Bool := fun i => if hi : i < b then cb ⟨i,hi⟩ else false
  have hp (s : Nat) (hs : s ≤ a) : (fun i : Fin s => fa i.val) =
      (fun i => ca (Fin.castLE hs i)) := by
    funext i
    have hi : i.val < a := by have := i.isLt; omega
    simp only [fa,dite_eq_left hi]
    rfl
  have hfa : A.halted (A.trace t (fun i => fa i.val) c) := by
    rw [hp t ht]; exact hh
  have hsame : A.trace t (fun i => fa i.val) c = A.trace a ca c := by
    rw [hp t ht]
    exact (A.trace_mono ht (by intro i; rfl) hh).symm
  obtain ⟨small,hsmall⟩ := chosen_at A B fa fb t b c (by
    intro s hs
    rw [hp s (by omega)]
    exact hfirst s hs) hfa
  have hfb : (fun i : Fin b => fb i.val) = cb := by
    funext i
    simp [fb,i.isLt]
  rw [hsame,hfb] at hsmall
  have hhalt : (machine A B).halted ((machine A B).trace (t+1+b) small (left A B c)) := by
    rw [hsmall]
    exact congrArg (fun q => (Sum.inr q : A.Q ⊕ B.Q)) hb
  let choices : Fin (a+1+b) → Bool := fun i =>
    if hi : i.val < t+1+b then small ⟨i.val,hi⟩ else false
  have heq := (machine A B).trace_mono (by omega : t+1+b ≤ a+1+b)
    (choices := small) (choices' := choices) (c := left A B c)
    (by intro i; simp [choices,i.isLt]) hhalt
  exact ⟨choices,heq.trans hsmall⟩

theorem chosen_post (A B : NTM n) (a b : Nat) (ca : Fin a → Bool) (cb : Fin b → Bool)
    (c : Cfg n A.Q) (R : Complexity.TapePred n) (ha : A.halted (A.trace a ca c))
    (hb : let d := B.trace b cb (boundary B (A.trace a ca c).input
        (A.trace a ca c).work (A.trace a ca c).output)
      B.halted d ∧ R d.input d.work d.output) :
    ∃ choices : Fin (a+1+b) → Bool,
      let d := (machine A B).trace (a+1+b) choices (left A B c)
      (machine A B).halted d ∧ R d.input d.work d.output := by
  obtain ⟨choices,hc⟩ := chosen A B a b ca cb c ha hb.1
  refine ⟨choices,?_,?_⟩
  · rw [hc]
    exact congrArg (fun q => (Sum.inr q : A.Q ⊕ B.Q)) hb.1
  · rw [hc]; exact hb.2

theorem chosen_tail (A B : NTM n) (a b : Nat) (ca : Fin a → Bool) (c : Cfg n A.Q)
    {Q R : Complexity.TapePred n}
    (ha : A.halted (A.trace a ca c))
    (hq : Q (A.trace a ca c).input (A.trace a ca c).work (A.trace a ca c).output)
    (hb : B.HoareTime Q R b)
    (hs : ∀ inp work out, Q inp work out →
      Q (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out)) :
    ∃ choices : Fin (a+1+b) → Bool,
      let d := (machine A B).trace (a+1+b) choices (left A B c)
      (machine A B).halted d ∧ R d.input d.work d.output := by
  apply chosen_post A B a b ca (fun _ => false) c R ha
  exact hb _ _ _ (hs _ _ _ hq) (fun _ => false)

theorem chosen_tail_init (A B : NTM n) (a b : Nat) (ca : Fin a → Bool)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    {Q R : Complexity.TapePred n}
    (ha : A.halted (A.trace a ca ⟨A.qstart,inp,work,out⟩))
    (hq : Q (A.trace a ca ⟨A.qstart,inp,work,out⟩).input
      (A.trace a ca ⟨A.qstart,inp,work,out⟩).work
      (A.trace a ca ⟨A.qstart,inp,work,out⟩).output)
    (hb : B.HoareTime Q R b)
    (hs : ∀ i w o, Q i w o →
      Q (transitionInput i) (fun j => transitionTape (w j)) (transitionTape o)) :
    ∃ choices : Fin (a+1+b) → Bool,
      let d := (machine A B).trace (a+1+b) choices
        ⟨(machine A B).qstart,inp,work,out⟩
      (machine A B).halted d ∧ R d.input d.work d.output :=
  chosen_tail A B a b ca ⟨A.qstart,inp,work,out⟩ ha hq hb hs

theorem prefix_fixed (A B : NTM n) (a b : Nat)
    (inp : Tape) (work : Fin n → Tape) (out : Tape)
    (inp' : Tape) (work' : Fin n → Tape) (out' : Tape)
    {P R : Complexity.TapePred n}
    (hp : P inp work out)
    (ha : A.HoareTime P (fun i w o => i = inp' ∧ w = work' ∧ o = out') a)
    (hi : transitionInput inp' = inp')
    (hw : (fun j => transitionTape (work' j)) = work')
    (ho : transitionTape out' = out')
    (hb : ∃ cb : Fin b → Bool,
      let d := B.trace b cb ⟨B.qstart,inp',work',out'⟩
      B.halted d ∧ R d.input d.work d.output) :
    ∃ choices : Fin (a+1+b) → Bool,
      let d := (machine A B).trace (a+1+b) choices ⟨(machine A B).qstart,inp,work,out⟩
      (machine A B).halted d ∧ R d.input d.work d.output := by
  obtain ⟨cb,hb⟩ := hb
  have h := ha inp work out hp (fun _ => false)
  obtain ⟨ha',hip,hwp,hop⟩ := h
  apply chosen_post A B a b (fun _ => false) cb ⟨A.qstart,inp,work,out⟩ R ha'
  simpa only [boundary,hip,hwp,hop,hi,hw,ho] using hb

end UnconstrainedPACDetection.VerifierNTMSequence

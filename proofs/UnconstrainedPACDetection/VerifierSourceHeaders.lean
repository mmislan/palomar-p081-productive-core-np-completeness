module

public import proofs.UnconstrainedPACDetection.VerifierSourcePositive

@[expose] public section

namespace UnconstrainedPACDetection.VerifierSourceHeaders
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierSourceHeaderGuard (unary)
open VerifierSourceGrammar (wire)
open VerifierSourceBranch (front)

def test : TM 3 := placeWorkTM 0 1 VerifierSourcePositive.machine

def tested (bits : List Bool) : Complexity.TM.TapePred 3 := fun inp work out =>
  VerifierSourcePositive.result bits inp (fun j => work (placeWorkIdx 0 1 j)) out ∧
    work 2 = wordTape [] ∧ AllTapesWF inp work out

private theorem run_wf {n : ℕ} {M : TM n} {c d : Cfg n M.Q} {t : ℕ}
    (h : M.reachesIn t c d) (hi : c.input.StartInvariant)
    (hw : ∀ j, (c.work j).StartInvariant) (ho : c.output.StartInvariant) :
    d.input.StartInvariant ∧ (∀ j, (d.work j).StartInvariant) ∧ d.output.StartInvariant := by
  induction h with
  | zero => exact ⟨hi,hw,ho⟩
  | step hs _ ih =>
    obtain ⟨hi,hw,ho⟩ := Tape.StartInvariant.step M hs hi hw ho
    exact ih hi hw ho

theorem test_hoare (bits : List Bool) : test.HoareTime
    (fun inp work out => inp = wordTape bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (tested bits) (7*bits.length+37) := by
  rintro inp work out ⟨rfl,rfl,rfl⟩
  obtain ⟨d,t,ht,hd,hh,hpost⟩ := VerifierSourcePositive.validation_hoare bits
    (wordTape bits) (fun _ => wordTape []) (wordTape []) ⟨rfl,rfl,rfl⟩
  let base : Fin 3 → Tape := fun _ => wordTape []
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierSourcePositive.machine 0 1 base hd (by
      intro j _; exact (VerifierReactionLoop.word_parked []).read_ne_start)
  have he : placeWorkCfg VerifierSourcePositive.machine 0 1 base
      ⟨VerifierSourcePositive.machine.qstart,wordTape bits,fun _ => wordTape [],wordTape []⟩ =
      (⟨test.qstart,wordTape bits,fun _ => wordTape [],wordTape []⟩ : Cfg 3 test.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  rw [he] at hp
  let final := placeWorkCfg VerifierSourcePositive.machine 0 1 base d
  have hsi := (Tape.StartInvariant.init_ofBool bits).move .right
  have hse := (Tape.StartInvariant.init_ofBool []).move .right
  obtain ⟨hfi,hfw,hfo⟩ := run_wf hp hsi (fun _ => hse) hse
  refine ⟨final,t,ht,hp,hh,?_,?_,hfi.1,hfi.2,fun j => (hfw j).1,fun j => (hfw j).2,hfo.1,hfo.2⟩
  · have hw : (fun j => final.work (placeWorkIdx 0 1 j)) = d.work := by
      funext j; exact placeWorkCfg_work_middle _ 0 1 base d j
    simpa only [hw, final, placeWorkCfg_input, placeWorkCfg_output] using hpost
  · exact placeWorkCfg_work_extra _ 0 1 base d 2 (by decide)

def before (bits : List Bool) : Complexity.TM.TapePred 3 := fun inp work out =>
  ∃ count m n ns, count ≤ bits.length ∧ wire (m::n::ns) = bits ∧
    (m::n::ns).length = count ∧ 0 < m ∧
    inp.HasBinarySuffix (BinaryFields.encodeField n.bits ++ wire ns) ∧
    work = ![unary count,wordTape m.bits,wordTape []] ∧ out = front true

def parsed (bits : List Bool) : Complexity.TM.TapePred 3 := fun inp work out =>
  ∃ count m n ns, count ≤ bits.length ∧ wire (m::n::ns) = bits ∧
    (m::n::ns).length = count ∧ 0 < m ∧ inp.HasBinarySuffix (wire ns) ∧
    work = ![unary count,wordTape m.bits,wordTape n.bits] ∧ out = front true

def rejected (bits : List Bool) : Complexity.TM.TapePred 3 := fun inp work out =>
  out = front false ∧ Parked inp ∧ (∀ j, Parked (work j)) ∧
    ¬ VerifierSourcePositive.HasPositiveHeader bits

theorem to_then (bits : List Bool) (inp : Tape) (work : Fin 3 → Tape) (out : Tape)
    (h : tested bits inp work out) (hv : out.cells 1 = Γ.one) :
    before bits (transitionInput inp) (fun j => transitionTape (work j)) ⟨1,out.cells⟩ := by
  obtain ⟨⟨b,ho,_,hyes⟩,h2,_⟩ := h
  have hb : b = true := by rw [ho] at hv; cases b <;> simp [one,Γ.ofBool] at hv ⊢
  subst b
  obtain ⟨count,m,ns,hc,he,hlen,hn,hm,hi,hw⟩ := hyes rfl
  cases ns with
  | nil => simp at hn
  | cons n ns =>
    have hwork : work = ![unary count,wordTape m.bits,wordTape []] := by
      funext j; fin_cases j
      · exact congrFun hw 0
      · exact congrFun hw 1
      · exact h2
    have hp : ∀ j, (work j).read ≠ .start := by
      rw [hwork]; intro j; fin_cases j
      all_goals exact (VerifierReactionLoop.word_parked _).read_ne_start
    have hout : out.read ≠ .start := by rw [ho]; change Γ.blank ≠ Γ.start; decide
    obtain ⟨hi',hw',_⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start hp hout
    refine ⟨count,m,n,ns,hc,he,hlen,hm,?_,hw'.trans hwork,?_⟩
    · simpa [hi', wire, BinaryFields.encode] using hi
    · rw [ho]; rfl

theorem to_else (bits : List Bool) (inp : Tape) (work : Fin 3 → Tape) (out : Tape)
    (h : tested bits inp work out) (hv : out.cells 1 ≠ Γ.one) :
    rejected bits (transitionInput inp) (fun j => transitionTape (work j)) ⟨1,out.cells⟩ := by
  obtain ⟨⟨b,ho,hacc,_⟩,_,hwf⟩ := h
  have hb : b = false := by rw [ho] at hv; cases b <;> simp [one,Γ.ofBool] at hv ⊢
  subst b
  have hs := hwf.transition
  refine ⟨?_,⟨hs.1,hs.2.1⟩,fun j => ⟨hs.2.2.1 j,hs.2.2.2.1 j⟩,?_⟩
  · rw [ho]; rfl
  · intro hpos; exact Bool.false_ne_true (hacc.mpr hpos)

theorem parse_hoare (bits : List Bool) : (VerifierFieldPlacement.machine 2 0).HoareTime
    (before bits) (parsed bits) (3*bits.length+5) := by
  rintro inp work out ⟨count,m,n,ns,hc,he,hlen,hm,hi,hw,ho⟩
  have hlenbits : n.bits.length ≤ bits.length := by
    have hh := congrArg List.length he
    change (BinaryFields.encodeField m.bits ++ (BinaryFields.encodeField n.bits ++ wire ns)).length = bits.length at hh
    simp only [List.length_append,BinaryFields.encodeField_length] at hh
    omega
  have hp := VerifierFieldPlacement.field_hoare 2 0 n.bits (wire ns)
    ![unary count,wordTape m.bits,wordTape []] (front true) rfl
    (by intro j hj; fin_cases j
        · exact (VerifierReactionLoop.word_parked _).read_ne_start
        · exact (VerifierReactionLoop.word_parked _).read_ne_start
        · exact False.elim (hj rfl))
    (VerifierSourceBranch.front_parked true).read_ne_start (VerifierSourceBranch.front_parked true).1
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := hp inp work out ⟨hi,hw,ho⟩
  refine ⟨d,t,by omega,hd,hh,count,m,n,ns,hc,he,hlen,hm,hdi,?_,hdo⟩
  rw [hdw]; funext j; fin_cases j <;> simp [VerifierFieldPlacement.slot,placeWorkIdx]

theorem reject_hoare (bits : List Bool) : (skipTM (n := 3)).HoareTime (rejected bits) (rejected bits) 1 := by
  intro inp work out h
  obtain ⟨ho,hi,hw,hn⟩ := h
  have hout : Parked out := by rw [ho]; exact VerifierSourceBranch.front_parked false
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := skipTM_hoareTime_frame inp work out hi hw hout _ _ _ ⟨rfl,rfl,rfl⟩
  exact ⟨d,t,ht,hd,hh,hdo.trans ho,hdi ▸ hi,hdw ▸ hw,hn⟩

theorem parsed_stable (bits : List Bool) : ∀ inp work out, parsed bits inp work out →
    parsed bits (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have horig := h
  obtain ⟨count,m,n,ns,_,_,_,_,hi,hw,ho⟩ := h
  have hp : ∀ j, (work j).read ≠ .start := by
    rw [hw]; intro j; fin_cases j
    all_goals exact (VerifierReactionLoop.word_parked _).read_ne_start
  have hout : out.read ≠ .start := by rw [ho]; exact (VerifierSourceBranch.front_parked true).read_ne_start
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start hp hout
  simpa only [hi',hw',ho'] using horig

theorem rejected_stable (bits : List Bool) : ∀ inp work out, rejected bits inp work out →
    rejected bits (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  obtain ⟨ho,hi,hw,hn⟩ := h
  have hout : out.read ≠ .start := by rw [ho]; exact (VerifierSourceBranch.front_parked false).read_ne_start
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start (fun j => (hw j).read_ne_start) hout
  simpa only [hi',hw',ho'] using (show rejected bits inp work out from ⟨ho,hi,hw,hn⟩)

def machine : TM 3 := ifTM test (VerifierFieldPlacement.machine 2 0) skipTM

theorem validation_hoare (bits : List Bool) : machine.HoareTime
    (fun inp work out => inp = wordTape bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (fun inp work out => parsed bits inp work out ∨ rejected bits inp work out) (10*bits.length+49) := by
  have hhead : ∀ inp work out, tested bits inp work out → out.head ≤ 2 := by
    rintro inp work out ⟨⟨b,ho,_,_⟩,_,_⟩; rw [ho]; rfl
  have h := ifTM_hoareTime _ _ _
    (post := fun inp work out => parsed bits inp work out ∨ rejected bits inp work out)
    (test_hoare bits) (fun _ _ _ h => h.2.2) hhead (to_then bits) (to_else bits)
    (parse_hoare bits) (reject_hoare bits)
    (fun inp work out h => Or.inl (parsed_stable bits inp work out h))
    (fun inp work out h => Or.inr (rejected_stable bits inp work out h))
  exact h.mono_bound (by omega)

def finish : TM 3 where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w o => (true,fun j => readBackWrite (w j),
    readBackWrite (Γ.ofBool (decide (w 2 ≠ .blank) && decide (o = .one))),
    idleDir i,fun j => idleDir (w j),.right)
  δ_right_of_start := by
    intro _ i w o
    exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,fun _ => rfl⟩

theorem finish_run (inp : Tape) (work : Fin 3 → Tape) (b : Bool)
    (hi : inp.read ≠ .start) (hw : ∀ j, Parked (work j)) :
    finish.reachesIn 1 ⟨false,inp,work,front b⟩
      ⟨true,inp,work,one .start (decide ((work 2).read ≠ .blank) && b)⟩ := by
  have hs : finish.step ⟨false,inp,work,front b⟩ =
      some ⟨true,inp,work,one .start (decide ((work 2).read ≠ .blank) && b)⟩ := by
    simp only [TM.step,finish,Bool.false_eq_true,↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · simp [idleDir,hi,Tape.move]
    · funext j; exact (hw j).writeAndMove_readBack_idle
    · cases b <;> by_cases hp : (work 2).cells (work 2).head = .blank <;>
        simp [front,one,Tape.read,Tape.writeAndMove,Tape.write,Tape.move,readBackWrite,Γ.ofBool,hp]
      all_goals funext i; by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp_all [Function.update]
  exact .step hs .zero

theorem word_read_nonblank (xs : List Bool) : (wordTape xs).read ≠ .blank ↔ xs ≠ [] := by
  cases xs with
  | nil => simp [wordTape,Tape.read,Tape.init,Tape.move]
  | cons b bs => cases b <;> simp [wordTape,Tape.read,Tape.init,Tape.move,Γ.ofBool]

def HasDimensions (bits : List Bool) : Prop :=
  ∃ m n ns, wire (m::n::ns) = bits ∧ 0 < m ∧ 0 < n

def ready (bits : List Bool) : Complexity.TM.TapePred 3 := fun inp work out =>
  ∃ b, out = one .start b ∧ (b = true ↔ HasDimensions bits) ∧
    (b = true → ∃ count m n ns, count ≤ bits.length ∧ wire (m::n::ns) = bits ∧
      (m::n::ns).length = count ∧ 0 < m ∧ 0 < n ∧ inp.HasBinarySuffix (wire ns) ∧
      work = ![unary count,wordTape m.bits,wordTape n.bits])

theorem dimensions_iff (bits : List Bool) (m n : ℕ) (ns : List ℕ)
    (he : wire (m::n::ns) = bits) (hm : 0 < m) : HasDimensions bits ↔ 0 < n := by
  constructor
  · rintro ⟨a,b,bs,hb,_,hp⟩
    have h := VerifierSourcePositive.wire_injective (hb.trans he.symm)
    have hn : b = n := (List.cons.inj (List.cons.inj h).2).1
    simpa only [hn] using hp
  · intro hn; exact ⟨m,n,ns,he,hm,hn⟩

def framedReady (bits : List Bool) : Complexity.TM.TapePred 3 := fun inp work out =>
  ready bits inp work out ∧ Parked inp ∧ ∀ j, Parked (work j)

theorem finish_framed_hoare (bits : List Bool) : finish.HoareTime
    (fun inp work out => parsed bits inp work out ∨ rejected bits inp work out) (framedReady bits) 1 := by
  intro inp work out h
  rcases h with h | h
  · obtain ⟨count,m,n,ns,hc,he,hlen,hm,hi,hw,ho⟩ := h
    subst work; subst out
    have hp : ∀ j, Parked (![unary count,wordTape m.bits,wordTape n.bits] j) := by
      intro j; fin_cases j <;> exact VerifierReactionLoop.word_parked _
    let b := decide ((wordTape n.bits).read ≠ .blank) && true
    have hb : b = true ↔ 0 < n := by
      simp only [b,Bool.and_true,decide_eq_true_eq,word_read_nonblank]
      exact VerifierActivationSemantics.bits_nonempty n
    refine ⟨_,1,le_rfl,finish_run inp _ true hi.read_ne_start hp,rfl,
      ⟨b,rfl,hb.trans (dimensions_iff bits m n ns he hm).symm,?_⟩,
      ⟨hi.1,hi.2.2.2⟩,hp⟩
    intro hyes
    exact ⟨count,m,n,ns,hc,he,hlen,hm,hb.mp hyes,hi,rfl⟩
  · obtain ⟨ho,hi,hw,hn⟩ := h
    subst out
    refine ⟨_,1,le_rfl,finish_run inp work false hi.read_ne_start hw,rfl,
      ⟨false,?_,?_,?_⟩,hi,hw⟩
    · simp only [Bool.and_false]
    · simp only [Bool.false_eq_true,false_iff]
      rintro ⟨m,n,ns,he,hm,_⟩
      exact hn ⟨m,n::ns,he,by simp,hm⟩
    · intro hbad; exact Bool.false_ne_true hbad |>.elim

theorem finish_hoare (bits : List Bool) : finish.HoareTime
    (fun inp work out => parsed bits inp work out ∨ rejected bits inp work out) (ready bits) 1 := by
  intro inp work out h
  obtain ⟨d,t,ht,hr,hh,hpost⟩ := finish_framed_hoare bits inp work out h
  exact ⟨d,t,ht,hr,hh,hpost.1⟩

def readyMachine : TM 3 := seqTM machine finish

theorem ready_framed_hoare (bits : List Bool) : readyMachine.HoareTime
    (fun inp work out => inp = wordTape bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (framedReady bits) (10*bits.length+51) := by
  have hs : ∀ inp work out, (parsed bits inp work out ∨ rejected bits inp work out) →
      parsed bits (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) ∨
      rejected bits (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
    intro inp work out h
    exact h.elim (fun h => Or.inl (parsed_stable bits inp work out h))
      (fun h => Or.inr (rejected_stable bits inp work out h))
  have h := seqTM_hoareTime _ _ (validation_hoare bits) hs (finish_framed_hoare bits)
  exact h.mono_bound (by omega)

theorem ready_hoare (bits : List Bool) : readyMachine.HoareTime
    (fun inp work out => inp = wordTape bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (ready bits) (10*bits.length+51) := by
  intro inp work out h
  obtain ⟨d,t,ht,hr,hh,hpost⟩ := ready_framed_hoare bits inp work out h
  exact ⟨d,t,ht,hr,hh,hpost.1⟩

end UnconstrainedPACDetection.VerifierSourceHeaders

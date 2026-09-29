module

public import proofs.UnconstrainedPACDetection.VerifierSourceReady
public import proofs.UnconstrainedPACDetection.VerifierFieldPlacement
public import proofs.Complexitylib.Models.TuringMachine.Registers.RegisterOps

@[expose] public section

namespace UnconstrainedPACDetection.VerifierSourceBranch
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierWitnessRegisters (pair)
open VerifierSourceHeaderGuard (unary)
open VerifierSourceGrammar (wire)

def front (b : Bool) : Tape := {one .start b with head := 1}

theorem front_parked (b : Bool) : Parked (front b) := by
  refine ⟨by rfl,?_⟩
  intro j hj
  have hz : j ≠ 0 := by omega
  by_cases h1 : j = 1 <;> cases b <;> simp [front,one,hz,h1,Γ.ofBool]

def branch (bits : List Bool) (v : Bool) : Complexity.TM.TapePred 2 :=
  fun inp work out => inp = wordTape bits ∧ ∃ count,
    count ≤ bits.length ∧ (v = true ↔ VerifierSourceHeaderValidation.HasHeaders bits) ∧
    (v = true → ∃ ns, wire ns = bits ∧ ns.length = count) ∧
    work = pair (unary count) (wordTape []) ∧ out = front v

def parsed (bits : List Bool) : Complexity.TM.TapePred 2 :=
  fun inp work out => ∃ count m ns, count ≤ bits.length ∧
    wire (m::ns) = bits ∧ (m::ns).length = count ∧ 0 < ns.length ∧
    inp.HasBinarySuffix (wire ns) ∧
    work = pair (unary count) (wordTape m.bits) ∧ out = front true

def machine : TM 2 := ifTM VerifierSourceReady.machine (VerifierFieldPlacement.machine 1 0) skipTM

theorem ready_wf (bits : List Bool) (inp : Tape) (work : Fin 2 → Tape) (out : Tape)
    (h : VerifierSourceReady.ready bits inp work out) : AllTapesWF inp work out := by
  obtain ⟨hin,count,v,_,hw,ho,_,_⟩ := h
  subst inp; subst work; subst out
  have hm := (Tape.StartInvariant.init_ofBool bits).move .right
  refine ⟨hm.1,hm.2,?_,?_,rfl,?_⟩
  · intro j; fin_cases j <;> rfl
  · intro j k hk; fin_cases j
    all_goals exact ((Tape.StartInvariant.init_ofBool _).move .right).2 k hk
  · intro j hj
    have hz : j ≠ 0 := by omega
    by_cases h1 : j = 1 <;> cases v <;> simp [one,hz,h1,Γ.ofBool]

theorem ready_head (bits : List Bool) (inp : Tape) (work : Fin 2 → Tape) (out : Tape)
    (h : VerifierSourceReady.ready bits inp work out) : out.head ≤ 2 := by
  obtain ⟨_,count,v,_,_,ho,_,_⟩ := h
  rw [ho]; rfl

theorem to_branch (bits : List Bool) (v : Bool) (inp : Tape) (work : Fin 2 → Tape) (out : Tape)
    (h : VerifierSourceReady.ready bits inp work out)
    (hv : out.cells 1 = Γ.one ↔ v = true) :
    branch bits v (transitionInput inp) (fun j => transitionTape (work j)) ⟨1,out.cells⟩ := by
  obtain ⟨hin,count,b,hc,hw,ho,hacc,hcounts⟩ := h
  have hb : b = v := by
    rw [ho] at hv
    cases b <;> cases v <;> simp [one,Γ.ofBool] at hv ⊢
  subst b
  have hp := VerifierSourceReady.register_parked bits work out
    ⟨count,v,hc,hw,ho,hacc,hcounts⟩
  have hi : inp.read ≠ .start := by rw [hin]; exact (VerifierReactionLoop.word_parked bits).read_ne_start
  obtain ⟨hi',hw',_⟩ := phaseTransition_eq_self_of_reads_ne_start hi
    (fun j => (hp.1 j).read_ne_start) hp.2.read_ne_start
  refine ⟨hi'.trans hin,count,hc,hacc,hcounts,hw'.trans hw,?_⟩
  rw [ho]; rfl

theorem parse_hoare (bits : List Bool) : (VerifierFieldPlacement.machine 1 0).HoareTime
    (branch bits true) (parsed bits) (3*bits.length+5) := by
  rintro inp work out ⟨hin,count,hc,hacc,hcounts,hw,ho⟩
  obtain ⟨ns,hn,hlen⟩ := hcounts rfl
  obtain ⟨ms,hm,hms⟩ := hacc.mp rfl
  have hsize : 2 ≤ ns.length := by
    have he := VerifierSourceHeaderValidation.same_wire_length ns ms (hn.trans hm.symm)
    omega
  cases ns with
  | nil => simp at hsize
  | cons m ns =>
    have hpos : 0 < ns.length := by simp only [List.length_cons] at hsize; omega
    have hin' : inp.HasBinarySuffix (BinaryFields.encodeField m.bits ++ wire ns) := by
      rw [hin,← hn]
      exact (Tape.init_move_right_hasBinaryString _).hasBinarySuffix
    have hlenbits : m.bits.length ≤ bits.length := by
      have he := congrArg List.length hn
      change (BinaryFields.encodeField m.bits ++ wire ns).length = bits.length at he
      simp only [List.length_append,BinaryFields.encodeField_length] at he
      omega
    have hparse := VerifierFieldPlacement.field_hoare 1 0 m.bits (wire ns)
      (pair (unary count) (wordTape [])) (front true) rfl
      (by intro j hj; fin_cases j
          · exact (VerifierReactionLoop.word_parked _).read_ne_start
          · exact False.elim (hj rfl))
      (front_parked true).read_ne_start (front_parked true).1
    obtain ⟨d,t,ht,hd,hh,hi',hw',ho'⟩ := hparse inp work out ⟨hin',hw,ho⟩
    refine ⟨d,t,by omega,hd,hh,count,m,ns,hc,hn,hlen,hpos,hi',?_,ho'⟩
    rw [hw']
    funext j; fin_cases j <;> simp [VerifierFieldPlacement.slot,placeWorkIdx,pair]

theorem reject_hoare (bits : List Bool) : (skipTM (n := 2)).HoareTime
    (branch bits false) (branch bits false) 1 := by
  intro inp work out h
  obtain ⟨hin,count,hc,hacc,hcounts,hw,ho⟩ := h
  have hi : Parked inp := by rw [hin]; exact VerifierReactionLoop.word_parked _
  have hp : ∀ j, Parked (work j) := by
    rw [hw]; intro j; fin_cases j
    all_goals exact VerifierReactionLoop.word_parked _
  have hout : Parked out := by rw [ho]; exact front_parked _
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := skipTM_hoareTime_frame inp work out hi hp hout _ _ _ ⟨rfl,rfl,rfl⟩
  exact ⟨d,t,ht,hd,hh,hdi.trans hin,count,hc,hacc,hcounts,hdw.trans hw,hdo.trans ho⟩

theorem parsed_stable (bits : List Bool) :
    ∀ inp work out, parsed bits inp work out →
      parsed bits (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have horig := h
  obtain ⟨count,m,ns,_,_,_,_,hi,hw,ho⟩ := h
  have hp : ∀ j, (work j).read ≠ .start := by
    rw [hw]; intro j; fin_cases j
    all_goals exact (VerifierReactionLoop.word_parked _).read_ne_start
  have hout : out.read ≠ .start := by rw [ho]; exact (front_parked _).read_ne_start
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start hp hout
  simpa only [hi',hw',ho'] using horig

theorem branch_stable (bits : List Bool) (v : Bool) :
    ∀ inp work out, branch bits v inp work out →
      branch bits v (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have horig := h
  obtain ⟨hi,count,_,_,_,hw,ho⟩ := h
  have hp : ∀ j, (work j).read ≠ .start := by
    rw [hw]; intro j; fin_cases j
    all_goals exact (VerifierReactionLoop.word_parked _).read_ne_start
  have hin : inp.read ≠ .start := by rw [hi]; exact (VerifierReactionLoop.word_parked _).read_ne_start
  have hout : out.read ≠ .start := by rw [ho]; exact (front_parked _).read_ne_start
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hin hp hout
  simpa only [hi',hw',ho'] using horig

theorem validation_hoare (bits : List Bool) : machine.HoareTime
    (fun inp work out => inp = wordTape bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (fun inp work out => parsed bits inp work out ∨ branch bits false inp work out)
    (7*bits.length+32) := by
  have h := ifTM_hoareTime _ _ _
    (post := fun inp work out => parsed bits inp work out ∨ branch bits false inp work out)
    (VerifierSourceReady.validation_hoare bits)
    (ready_wf bits) (ready_head bits)
    (fun inp work out h hv => to_branch bits true inp work out h (by simp [hv]))
    (fun inp work out h hv => to_branch bits false inp work out h (by simp [hv]))
    (parse_hoare bits) (reject_hoare bits)
    (fun inp work out h => Or.inl (parsed_stable bits inp work out h))
    (fun inp work out h => Or.inr (branch_stable bits false inp work out h))
  exact h.mono_bound (by omega)

def finish : TM 2 where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w o => (true,fun j => readBackWrite (w j),readBackWrite o,
    idleDir i,fun j => idleDir (w j),.right)
  δ_right_of_start := by
    intro _ i w o
    exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,fun _ => rfl⟩

theorem finish_run (inp : Tape) (work : Fin 2 → Tape) (v : Bool)
    (hi : inp.read ≠ .start) (hw : ∀ j, Parked (work j)) :
    finish.reachesIn 1 ⟨false,inp,work,front v⟩ ⟨true,inp,work,one .start v⟩ := by
  have hs : finish.step ⟨false,inp,work,front v⟩ = some ⟨true,inp,work,one .start v⟩ := by
    simp only [TM.step,finish,Bool.false_eq_true,↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · simp [idleDir,hi,Tape.move]
    · funext j
      exact (hw j).writeAndMove_readBack_idle
    · rw [writeAndMove_readBack _ (front_parked v).read_ne_start]
      rfl
  exact .step hs .zero

def result (bits : List Bool) : Complexity.TM.TapePred 2 :=
  fun inp work out => ∃ v, out = one .start v ∧
    (parsed bits inp work (front v) ∨ branch bits false inp work (front v))

theorem finish_hoare (bits : List Bool) : finish.HoareTime
    (fun inp work out => parsed bits inp work out ∨ branch bits false inp work out)
    (result bits) 1 := by
  intro inp work out h
  have hframe : ∃ v, out = front v ∧ inp.read ≠ .start ∧ (∀ j, Parked (work j)) := by
    rcases h with h | h
    · obtain ⟨count,m,ns,_,_,_,_,hi,hw,ho⟩ := h
      refine ⟨true,ho,?_,?_⟩
      · exact hi.read_ne_start
      · rw [hw]; intro j; fin_cases j
        all_goals exact VerifierReactionLoop.word_parked _
    · obtain ⟨hi,count,_,_,_,hw,ho⟩ := h
      refine ⟨false,ho,?_,?_⟩
      · rw [hi]; exact (VerifierReactionLoop.word_parked _).read_ne_start
      · rw [hw]; intro j; fin_cases j
        all_goals exact VerifierReactionLoop.word_parked _
  obtain ⟨v,ho,hi,hw⟩ := hframe
  subst out
  exact ⟨_,1,le_rfl,finish_run inp work v hi hw,rfl,v,rfl,h⟩

def readyMachine : TM 2 := seqTM machine finish

theorem ready_hoare (bits : List Bool) : readyMachine.HoareTime
    (fun inp work out => inp = wordTape bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (result bits) (7*bits.length+34) := by
  have hs : ∀ inp work out,
      (parsed bits inp work out ∨ branch bits false inp work out) →
      parsed bits (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) ∨
      branch bits false (transitionInput inp) (fun j => transitionTape (work j)) (transitionTape out) := by
    intro inp work out h
    exact h.elim (fun h => Or.inl (parsed_stable bits inp work out h))
      (fun h => Or.inr (branch_stable bits false inp work out h))
  have h := seqTM_hoareTime _ _ (validation_hoare bits) hs (finish_hoare bits)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierSourceBranch

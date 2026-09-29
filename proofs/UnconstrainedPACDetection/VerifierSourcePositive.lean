module

public import proofs.UnconstrainedPACDetection.VerifierSourceBranch
public import proofs.UnconstrainedPACDetection.VerifierActivationSemantics

@[expose] public section

namespace UnconstrainedPACDetection.VerifierSourcePositive
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierWitnessRegisters (pair)
open VerifierSourceHeaderGuard (unary)
open VerifierSourceGrammar (wire)

inductive Phase where
  | first | commit (present : Bool) | done
  deriving DecidableEq, Fintype

def gate : TM 2 where
  Q := Phase
  qstart := .first
  qhalt := .done
  δ := fun q i w o => match q with
    | .first => (.commit (decide (w 1 ≠ .blank)),fun j => readBackWrite (w j),
        readBackWrite o,idleDir i,fun j => idleDir (w j),VerifierAccumulate.markerDir o .left)
    | .commit present => (.done,fun j => readBackWrite (w j),
        readBackWrite (Γ.ofBool (present && decide (o = .one))),
        idleDir i,fun j => idleDir (w j),.right)
    | .done => allIdle .done i w o
  δ_right_of_start := by
    intro q i w o
    cases q with
    | first => exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,
        fun h => by simp [VerifierAccumulate.markerDir,h]⟩
    | commit _ => exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,fun _ => rfl⟩
    | done => exact rightOfStart_allIdle i w o

theorem gate_run (count : ℕ) (bits : List Bool) (b : Bool) (inp : Tape)
    (hi : inp.read ≠ .start) :
    gate.reachesIn 2 ⟨.first,inp,pair (unary count) (wordTape bits),one .start b⟩
      ⟨.done,inp,pair (unary count) (wordTape bits),one .start (decide (bits ≠ []) && b)⟩ := by
  have hir : inp.cells inp.head ≠ .start := hi
  let mid : Cfg 2 Phase := ⟨.commit (decide (bits ≠ [])),inp,
    pair (unary count) (wordTape bits),{one .start b with head := 1}⟩
  have h1 : gate.step ⟨.first,inp,pair (unary count) (wordTape bits),one .start b⟩ = some mid := by
    cases count <;> cases bits with
    | nil =>
      cases b <;> simp [TM.step,gate,mid,pair,unary,wordTape,one,Tape.read,Tape.init,
        Tape.move,Tape.writeAndMove,Tape.write,VerifierAccumulate.markerDir,idleDir,hir,
        readBackWrite,Γ.ofBool,List.replicate_succ]
      all_goals funext j; fin_cases j <;> simp
    | cons a bits =>
      cases a <;> cases b <;> simp [TM.step,gate,mid,pair,unary,wordTape,one,Tape.read,Tape.init,
        Tape.move,Tape.writeAndMove,Tape.write,VerifierAccumulate.markerDir,idleDir,hir,
        readBackWrite,Γ.ofBool,List.replicate_succ]
      all_goals funext j; fin_cases j <;> simp
  have h2 : gate.step mid = some
      ⟨.done,inp,pair (unary count) (wordTape bits),one .start (decide (bits ≠ []) && b)⟩ := by
    cases count <;> cases bits with
    | nil =>
      cases b <;> simp [TM.step,gate,mid,pair,unary,wordTape,one,Tape.read,Tape.init,
        Tape.move,Tape.writeAndMove,Tape.write,idleDir,hir,readBackWrite,Γ.ofBool,List.replicate_succ]
      all_goals try constructor
      all_goals first | (funext j; fin_cases j <;> simp) |
        (funext i; by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> simp_all [Function.update])
    | cons a bits =>
      cases a <;> cases b <;> simp [TM.step,gate,mid,pair,unary,wordTape,one,Tape.read,Tape.init,
        Tape.move,Tape.writeAndMove,Tape.write,idleDir,hir,readBackWrite,Γ.ofBool,List.replicate_succ]
      all_goals funext j; fin_cases j <;> simp
  exact .step h1 (.step h2 .zero)

def HasPositiveHeader (bits : List Bool) : Prop :=
  ∃ m ns, wire (m::ns) = bits ∧ 0 < ns.length ∧ 0 < m

def result (bits : List Bool) : Complexity.TM.TapePred 2 :=
  fun inp work out => ∃ b, out = one .start b ∧
    (b = true ↔ HasPositiveHeader bits) ∧
    (b = true → ∃ count m ns, count ≤ bits.length ∧ wire (m::ns) = bits ∧
      (m::ns).length = count ∧ 0 < ns.length ∧ 0 < m ∧
      inp.HasBinarySuffix (wire ns) ∧ work = pair (unary count) (wordTape m.bits))

theorem wire_injective : Function.Injective wire := by
  intro ns ms he
  have h := congrArg BinaryFields.decode he
  simp only [wire,BinaryFields.decode_encode,Option.some.injEq] at h
  have hr := congrArg (List.map BinaryFields.readNat) h
  simpa [List.map_map,Function.comp_def] using hr

theorem positive_iff (bits : List Bool) (m : ℕ) (ns : List ℕ)
    (he : wire (m::ns) = bits) (hn : 0 < ns.length) :
    HasPositiveHeader bits ↔ 0 < m := by
  constructor
  · rintro ⟨a,as,ha,_,hp⟩
    have hs := wire_injective (ha.trans he.symm)
    have hm : a = m := (List.cons.inj hs).1
    simpa only [hm] using hp
  · intro hp; exact ⟨m,ns,he,hn,hp⟩

theorem front_injective {a b : Bool}
    (he : VerifierSourceBranch.front a = VerifierSourceBranch.front b) : a = b := by
  have h := congrArg (fun t : Tape => t.cells 1) he
  cases a <;> cases b <;> simp [VerifierSourceBranch.front,one,Γ.ofBool] at h ⊢

theorem gate_hoare (bits : List Bool) : gate.HoareTime
    (VerifierSourceBranch.result bits) (result bits) 2 := by
  rintro inp work out ⟨b,ho,h⟩
  rcases h with h | h
  · obtain ⟨count,m,ns,hc,he,hlen,hn,hi,hw,hb⟩ := h
    have hb' : b = true := front_injective hb
    subst b; subst work; subst out
    let v := decide (m.bits ≠ []) && true
    have hv : v = true ↔ 0 < m := by
      simp only [v,Bool.and_true,decide_eq_true_eq]
      exact VerifierActivationSemantics.bits_nonempty m
    refine ⟨_,2,le_rfl,gate_run count m.bits true inp hi.read_ne_start,rfl,
      v,rfl,hv.trans (positive_iff bits m ns he hn).symm,?_⟩
    intro hyes
    exact ⟨count,m,ns,hc,he,hlen,hn,hv.mp hyes,hi,rfl⟩
  · obtain ⟨hi,count,hc,hacc,_,hw,hb⟩ := h
    have hb' : b = false := front_injective hb
    subst b; subst work; subst out
    have hread : inp.read ≠ .start := by rw [hi]; exact (VerifierReactionLoop.word_parked _).read_ne_start
    have hno : ¬ HasPositiveHeader bits := by
      rintro ⟨m,ns,he,hn,_⟩
      have hh : VerifierSourceHeaderValidation.HasHeaders bits :=
        ⟨m::ns,he,by simp only [List.length_cons]; omega⟩
      exact Bool.false_ne_true (hacc.mpr hh)
    refine ⟨_,2,le_rfl,gate_run count [] false inp hread,rfl,false,rfl,?_,?_⟩
    · simp only [Bool.false_eq_true,false_iff]; exact hno
    · intro hbad; exact Bool.false_ne_true hbad |>.elim

theorem before_stable (bits : List Bool) :
    ∀ inp work out, VerifierSourceBranch.result bits inp work out →
      VerifierSourceBranch.result bits (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have horig := h
  obtain ⟨b,ho,h⟩ := h
  have hh : inp.read ≠ .start ∧ ∀ j, (work j).read ≠ .start := by
    rcases h with h | h
    · obtain ⟨count,m,ns,_,_,_,_,hi,hw,_⟩ := h
      refine ⟨hi.read_ne_start,?_⟩
      rw [hw]; intro j; fin_cases j
      all_goals exact (VerifierReactionLoop.word_parked _).read_ne_start
    · obtain ⟨hi,count,_,_,_,hw,_⟩ := h
      constructor
      · rw [hi]; exact (VerifierReactionLoop.word_parked _).read_ne_start
      · rw [hw]; intro j; fin_cases j
        all_goals exact (VerifierReactionLoop.word_parked _).read_ne_start
  have hout : out.read ≠ .start := by rw [ho]; change Γ.blank ≠ Γ.start; decide
  obtain ⟨hi,hw,ho⟩ := phaseTransition_eq_self_of_reads_ne_start hh.1 hh.2 hout
  simpa only [hi,hw,ho] using horig

def machine : TM 2 := seqTM VerifierSourceBranch.readyMachine gate

theorem validation_hoare (bits : List Bool) : machine.HoareTime
    (fun inp work out => inp = wordTape bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (result bits) (7*bits.length+37) := by
  have h := seqTM_hoareTime _ _ (VerifierSourceBranch.ready_hoare bits)
    (before_stable bits) (gate_hoare bits)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierSourcePositive

module

public import proofs.UnconstrainedPACDetection.VerifierSourceHeaderGuard

@[expose] public section

namespace UnconstrainedPACDetection.VerifierSourceHeaderValidation
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierWitnessRegisters (pair)
open VerifierSourceGrammar (wire)

def HasHeaders (bits : List Bool) : Prop :=
  ∃ ns : List ℕ, wire ns = bits ∧ 2 ≤ ns.length

theorem same_wire_length (ns ms : List ℕ) (h : wire ns = wire ms) : ns.length = ms.length := by
  have hh := congrArg (fun bits => (VerifierSourceGrammar.run .boundary bits).2.1) h
  simpa only [VerifierSourceGrammar.wire_run] using hh

theorem meaning_guard (bits : List Bool) (count : ℕ) (b : Bool)
    (h : VerifierSourceRegisters.Meaning bits count b) :
    (decide (2 ≤ count) && b) = true ↔ HasHeaders bits := by
  rw [Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hc,hb⟩
    obtain ⟨ns,hn,hlen⟩ := h.2.2 hb
    exact ⟨ns,hn,by omega⟩
  · rintro ⟨ns,hn,hlen⟩
    have hb := h.2.1.mpr ⟨ns,hn⟩
    obtain ⟨ms,hm,hcount⟩ := h.2.2 hb
    have he := same_wire_length ns ms (hn.trans hm.symm)
    exact ⟨by omega,hb⟩

def after (bits : List Bool) : Complexity.TM.TapePred 2 :=
  fun inp work out => inp.HasBinarySuffix [] ∧ ∃ count b,
    VerifierSourceRegisters.Meaning bits count b ∧
    work = pair (VerifierSourceHeaderGuard.unary count) (wordTape []) ∧
    out = one .start (decide (2 ≤ count) && b)

def machine : TM 2 := seqTM VerifierSourceRegisters.machine VerifierSourceHeaderGuard.gate

theorem stable (bits : List Bool) :
    ∀ inp work out, VerifierSourceRegisters.stage bits true inp work out →
      VerifierSourceRegisters.stage bits true (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have horig := h
  obtain ⟨hi,count,b,_,hw,ho⟩ := h
  have hwork : ∀ j, (work j).read ≠ .start := by
    rw [hw]; intro j; fin_cases j
    all_goals exact (VerifierReactionLoop.word_parked _).read_ne_start
  have hout : out.read ≠ .start := by rw [ho]; change Γ.blank ≠ Γ.start; decide
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start hwork hout
  simpa only [hi',hw',ho'] using horig

theorem gate_hoare (bits : List Bool) :
    VerifierSourceHeaderGuard.gate.HoareTime (VerifierSourceRegisters.stage bits true)
      (after bits) 2 := by
  rintro inp work out ⟨hi,count,b,hm,hw,ho⟩
  subst work; subst out
  have hr := VerifierSourceHeaderGuard.gate_run count b inp hi.read_ne_start
  exact ⟨_,2,le_rfl,hr,rfl,hi,count,b,hm,rfl,rfl⟩

theorem validation_hoare (bits : List Bool) : machine.HoareTime
    (fun inp work out => inp.HasBinarySuffix bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (after bits) (2*bits.length+8) := by
  have h := seqTM_hoareTime _ _ (VerifierSourceRegisters.validation_hoare bits) (stable bits) (gate_hoare bits)
  exact h.mono_bound (by omega)

/-- Uniform raw-input contract: acceptance means at least two canonical unsigned
fields, and the preserved unary register is their exact count on acceptance. -/
theorem checked_hoare (bits : List Bool) : machine.HoareTime
    (fun inp work out => inp.HasBinarySuffix bits ∧ work = (fun _ => wordTape []) ∧ out = wordTape [])
    (fun inp work out => inp.HasBinarySuffix [] ∧ ∃ count v,
      count ≤ bits.length ∧
      work = pair (VerifierSourceHeaderGuard.unary count) (wordTape []) ∧
      out = one .start v ∧ (v = true ↔ HasHeaders bits) ∧
      (v = true → ∃ ns, wire ns = bits ∧ ns.length = count)) (2*bits.length+8) := by
  intro inp work out h
  obtain ⟨d,t,ht,hd,hh,hi,count,b,hm,hw,ho⟩ := validation_hoare bits inp work out h
  refine ⟨d,t,ht,hd,hh,hi,count,decide (2 ≤ count) && b,hm.1,hw,ho,
    meaning_guard bits count b hm,?_⟩
  intro hv
  have hb : decide (2 ≤ count) = true ∧ b = true := by
    simpa only [Bool.and_eq_true] using hv
  exact hm.2.2 hb.2

theorem accepted_has_two_fields (bits : List Bool) (h : HasHeaders bits) :
    ∃ (m n : ℕ) (ns : List ℕ),
      bits = BinaryFields.encodeField m.bits ++ BinaryFields.encodeField n.bits ++ wire ns := by
  obtain ⟨ns,hn,hlen⟩ := h
  cases ns with
  | nil => simp at hlen
  | cons m ns =>
    cases ns with
    | nil => simp at hlen
    | cons n ns =>
      refine ⟨m,n,ns,?_⟩
      subst bits
      simp [wire,BinaryFields.encode,List.append_assoc]

end UnconstrainedPACDetection.VerifierSourceHeaderValidation

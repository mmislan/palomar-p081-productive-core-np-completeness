module

public import proofs.UnconstrainedPACDetection.VerifierDimensionGuard
public import proofs.UnconstrainedPACDetection.VerifierDimensionData

@[expose] public section

namespace UnconstrainedPACDetection.VerifierRawDimensions
open Complexity Complexity.TM
open VerifierVerdictAnd (one)

def after (src wit : List Bool) : Complexity.TM.TapePred 11 := fun inp work out =>
  (VerifierJointPrepare.after src wit inp work (one .start false) ∧ out = one .start false) ∨
  ∃ base m n k l, VerifierJointPrepare.after src wit inp base (one .start true) ∧
    VerifierDimensionData.Operands src wit base m n k l ∧
    VerifierDimensionCompare.bothAfter m.bits (VerifierUnaryBinary.digits k)
      n.bits (VerifierUnaryBinary.digits l) true inp base inp work out

theorem guard_hoare (src wit : List Bool) : VerifierDimensionGuard.machine.HoareTime
    (VerifierJointPrepare.after src wit) (after src wit) (2*src.length+2*wit.length+13) := by
  intro inp work out h
  obtain ⟨hpi,hpw,v,ho⟩ := VerifierDimensionData.parked src wit h
  subst out
  cases v with
  | false =>
    obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := VerifierDimensionGuard.rejected_hoare
      inp work hpi.read_ne_start hpw inp work (one .start false) ⟨rfl,rfl,rfl⟩
    refine ⟨d,t,by omega,hr,hh,Or.inl ⟨?_,hdo⟩⟩
    simpa only [hdi,hdw] using h
  | true =>
    obtain ⟨m,n,k,l,hparams⟩ := VerifierDimensionData.accepted_operands src wit h
    have hbound := VerifierDimensionData.comparison_bound src wit work m n k l hparams
    obtain ⟨hkl,hm,hn,h1,h2,h3,h6,h10⟩ := hparams
    obtain ⟨d,t,ht,hr,hh,hpost⟩ := VerifierDimensionGuard.accepted_hoare
      m.bits (VerifierUnaryBinary.digits k) n.bits (VerifierUnaryBinary.digits l)
      inp work hpi.read_ne_start hpw h3 h1 h6 h2 h10 inp work (one .start true) ⟨rfl,rfl,rfl⟩
    have hcopy := hpost
    obtain ⟨mid,_,hsecond⟩ := hcopy
    have hi := hsecond.1
    refine ⟨d,t,by omega,hr,hh,Or.inr ⟨work,m,n,k,l,?_,?_,?_⟩⟩
    · simpa only [hi] using h
    · exact ⟨hkl,hm,hn,h1,h2,h3,h6,h10⟩
    · simpa only [hi] using hpost

theorem prepared_stable (src wit : List Bool) : ∀ inp work out,
    VerifierJointPrepare.after src wit inp work out →
    VerifierJointPrepare.after src wit (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  obtain ⟨hi,hw,v,ho⟩ := VerifierDimensionData.parked src wit h
  have hout : out.read ≠ .start := by rw [ho]; change Γ.blank ≠ Γ.start; decide
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start
    (fun j => (hw j).read_ne_start) hout
  simpa only [hi',hw',ho'] using h

def machine : TM 11 := seqTM VerifierJointPrepare.machine VerifierDimensionGuard.machine

theorem validation_hoare (src wit : List Bool) : machine.HoareTime
    (VerifierJointPrepare.before src wit) (after src wit)
    (12*src.length+40*(wit.length+1)^2+4*wit.length+84) := by
  have h := seqTM_hoareTime _ _ (VerifierJointPrepare.validation_hoare src wit)
    (prepared_stable src wit) (guard_hoare src wit)
  exact h.mono_bound (by omega)

theorem accepted_matches (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape}
    (h : after src wit inp work (one .start true)) :
    ∃ base m n k l, VerifierJointPrepare.after src wit inp base (one .start true) ∧
      VerifierDimensionData.Operands src wit base m n k l ∧ m = k ∧ n = l := by
  rcases h with ⟨_,hbad⟩ | ⟨base,m,n,k,l,hprep,hparams,hcomp⟩
  · have hfalse := VerifierDimensionData.one_injective hbad
    cases hfalse
  · obtain ⟨b,hout,hiff⟩ := VerifierDimensionCompare.numeric_verdict m n k l true inp base hcomp
    have hb : b = true := (VerifierDimensionData.one_injective hout).symm
    obtain ⟨hm,hn,_⟩ := hiff.mp hb
    exact ⟨base,m,n,k,l,hprep,hparams,hm,hn⟩

end UnconstrainedPACDetection.VerifierRawDimensions

module

public import proofs.UnconstrainedPACDetection.VerifierCardinalityGuard

@[expose] public section

namespace UnconstrainedPACDetection.VerifierRawCardinality
open Complexity Complexity.TM
open VerifierVerdictAnd (one)

def after (src wit : List Bool) : Complexity.TM.TapePred 11 := fun inp work out =>
  (VerifierRawDimensions.after src wit inp work (one .start false) ∧ out = one .start false) ∨
  ∃ base q m n, VerifierRawDimensions.after src wit inp base (one .start true) ∧
    VerifierCardinalityData.Registers src wit base q m n ∧
    VerifierFieldCardinalityCheck.after q (2*m*n+2) true inp
      (VerifierFieldCardinality.cleared (VerifierFieldCardinalityCount.frame base (2*m*n+2))) inp work out

theorem guard_hoare (src wit : List Bool) : VerifierCardinalityGuard.machine.HoareTime
    (VerifierRawDimensions.after src wit) (after src wit)
    (4*opBudget (2*(wit.length+1)^2)+src.length+2*(wit.length+1)^2+17) := by
  intro inp work out h
  obtain ⟨hi,hp,v,ho⟩ := VerifierCardinalityData.parked src wit h
  subst out
  cases v with
  | false =>
    obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := VerifierCardinalityGuard.rejected_hoare
      inp work hi.read_ne_start hp inp work (one .start false) ⟨rfl,rfl,rfl⟩
    refine ⟨d,t,by omega,hr,hh,Or.inl ⟨?_,hdo⟩⟩
    simpa only [hdi,hdw] using h
  | true =>
    obtain ⟨q,m,n,hregs⟩ := VerifierCardinalityData.accepted_registers src wit h
    obtain ⟨hq,hmn,h0,h4,h5,h8,h10⟩ := hregs
    have hbody := VerifierFieldCardinality.validation_hoare q m n src.length wit.length true
      inp work hi hp h0 h4 h5 h8 h10 hq (by omega) (by omega)
    obtain ⟨d,t,ht,hr,hh,hpost⟩ := VerifierCardinalityGuard.accepted_hoare inp work hi.read_ne_start
      hp _ _ hbody inp work (one .start true) ⟨rfl,rfl,rfl⟩
    have hdi := hpost.1
    refine ⟨d,t,by omega,hr,hh,Or.inr ⟨work,q,m,n,?_,⟨hq,hmn,h0,h4,h5,h8,h10⟩,?_⟩⟩
    · simpa only [hdi] using h
    · simpa only [hdi] using hpost

theorem dimensions_stable (src wit : List Bool) : ∀ inp work out,
    VerifierRawDimensions.after src wit inp work out →
    VerifierRawDimensions.after src wit (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  obtain ⟨hi,hw,v,ho⟩ := VerifierCardinalityData.parked src wit h
  have hout : out.read ≠ .start := by rw [ho]; change Γ.blank ≠ Γ.start; decide
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start
    (fun j => (hw j).read_ne_start) hout
  simpa only [hi',hw',ho'] using h

def machine : TM 11 := seqTM VerifierRawDimensions.machine VerifierCardinalityGuard.machine

theorem validation_hoare (src wit : List Bool) : machine.HoareTime
    (VerifierJointPrepare.before src wit) (after src wit)
    (13*src.length+42*(wit.length+1)^2+4*wit.length+4*opBudget (2*(wit.length+1)^2)+102) := by
  have h := seqTM_hoareTime _ _ (VerifierRawDimensions.validation_hoare src wit)
    (dimensions_stable src wit) (guard_hoare src wit)
  exact h.mono_bound (by omega)

theorem accepted_cardinality (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape}
    (h : after src wit inp work (one .start true)) :
    ∃ base q m n, VerifierRawDimensions.after src wit inp base (one .start true) ∧
      VerifierCardinalityData.Registers src wit base q m n ∧ q = 2*m*n+2 := by
  rcases h with ⟨_,hbad⟩ | ⟨base,q,m,n,hprep,hregs,hcheck⟩
  · have hfalse := VerifierDimensionData.one_injective hbad; cases hfalse
  · obtain ⟨b,hout,hiff⟩ := VerifierFieldCardinalityCheck.numeric_verdict q (2*m*n+2) true inp _ hcheck
    have hb : b = true := (VerifierDimensionData.one_injective hout).symm
    exact ⟨base,q,m,n,hprep,hregs,(hiff.mp hb).1⟩

end UnconstrainedPACDetection.VerifierRawCardinality

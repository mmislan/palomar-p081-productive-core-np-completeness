module

public import proofs.UnconstrainedPACDetection.VerifierFieldCardinality

@[expose] public section

namespace UnconstrainedPACDetection.VerifierCardinalityData
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)

def Registers (src wit : List Bool) (work : Fin 11 → Tape) (q m n : ℕ) : Prop :=
  q ≤ src.length ∧ m+n ≤ wit.length ∧ work 0 = regTape q ∧ work 4 = regTape 1 ∧
    work 5 = regTape m ∧ work 8 = regTape n ∧ work 10 = regTape 0

theorem prepared_registers (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape}
    (h : VerifierJointPrepare.after src wit inp work (one .start true)) :
    ∃ q m n, Registers src wit work q m n := by
  obtain ⟨source,prior,hsource,_,m,n,b,wt,hmeaning,_,_,hw,ho⟩ := h
  have hb : b = true ∧ prior = true := by
    simpa only [↓reduceIte,Bool.and_eq_true] using (VerifierDimensionData.one_injective ho).symm
  obtain ⟨hb,hprior⟩ := hb
  subst b; subst prior
  obtain ⟨p,hp,_,haccepted⟩ := hsource.1
  have hp' : p = true := (VerifierDimensionData.one_injective hp).symm
  subst p
  obtain ⟨q,a,c,ns,hq,_,_,_,_,_,hs⟩ := haccepted rfl
  refine ⟨q,m,n,hq,hmeaning.1,?_,?_,?_,?_,?_⟩
  all_goals rw [hw,hs]
  · exact VerifierCountPrepare.unary_eq_reg q
  · exact VerifierCountPrepare.unary_eq_reg 1
  · exact VerifierCountPrepare.unary_eq_reg m
  · exact VerifierCountPrepare.unary_eq_reg n
  · exact VerifierCountPrepare.unary_eq_reg 0

theorem preserved_slots (x₁ y₁ x₂ y₂ : List Bool) (v : Bool) (inp₀ : Tape) (base : Fin 11 → Tape)
    {inp : Tape} {work : Fin 11 → Tape} {out : Tape}
    (h : VerifierDimensionCompare.bothAfter x₁ y₁ x₂ y₂ v inp₀ base inp work out)
    (j : Fin 11) (hj : j = 0 ∨ j = 4 ∨ j = 5 ∨ j = 8 ∨ j = 10) : work j = base j := by
  obtain ⟨mid,⟨_,a,b,_,_,_,_,hmid,_⟩,_,c,d,_,_,_,_,hw,_⟩ := h
  rcases hj with h | h | h | h | h
  all_goals subst j; rw [hw,hmid]; rfl

theorem accepted_registers (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape}
    (h : VerifierRawDimensions.after src wit inp work (one .start true)) :
    ∃ q m n, Registers src wit work q m n := by
  rcases h with ⟨_,hbad⟩ | ⟨base,a,b,k,l,hprep,_,hcomp⟩
  · have hfalse := VerifierDimensionData.one_injective hbad; cases hfalse
  · obtain ⟨q,m,n,hq,hmn,h0,h4,h5,h8,h10⟩ := prepared_registers src wit hprep
    have hprotected := preserved_slots _ _ _ _ _ _ _ hcomp
    refine ⟨q,m,n,hq,hmn,?_,?_,?_,?_,?_⟩
    · exact (hprotected 0 (by simp)).trans h0
    · exact (hprotected 4 (by simp)).trans h4
    · exact (hprotected 5 (by simp)).trans h5
    · exact (hprotected 8 (by simp)).trans h8
    · exact (hprotected 10 (by simp)).trans h10

theorem parked (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape} {out : Tape}
    (h : VerifierRawDimensions.after src wit inp work out) :
    Parked inp ∧ (∀ j, Parked (work j)) ∧ ∃ v, out = one .start v := by
  rcases h with ⟨hprep,ho⟩ | ⟨base,m,n,k,l,hprep,_,hcomp⟩
  · obtain ⟨hi,hw,_⟩ := VerifierDimensionData.parked src wit hprep
    exact ⟨hi,hw,false,ho⟩
  · obtain ⟨hi,hbase,_⟩ := VerifierDimensionData.parked src wit hprep
    obtain ⟨mid,hfirst,hsecond⟩ := hcomp
    have hmid := VerifierDimensionCompare.after_parked false _ _ _ inp base hbase hfirst
    have hwork := VerifierDimensionCompare.after_parked true _ _ _ inp mid hmid hsecond
    obtain ⟨_,a,b,_,_,_,_,_,ho⟩ := hsecond
    exact ⟨hi,hwork,_,ho⟩

end UnconstrainedPACDetection.VerifierCardinalityData

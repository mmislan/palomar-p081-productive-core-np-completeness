module

public import proofs.UnconstrainedPACDetection.VerifierTypedRecovery

@[expose] public section

namespace UnconstrainedPACDetection.VerifierRawFrame
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)

theorem prepared_frame (src wit : List Bool) (s : BinarySourceData.DenseSource)
    (w : BinaryWitnessData.Witness)
    (hs : BinarySourceData.decode src = some s) (hw : BinaryWitnessData.decode wit = some w)
    {inp : Tape} {work : Fin 11 → Tape}
    (h : VerifierJointPrepare.after src wit inp work (one .start true)) :
    inp.HasBinarySuffix (BinaryFields.encode (s.values.map Nat.bits)) ∧
      work 5 = regTape w.mask.length ∧ work 8 = regTape w.flow.length ∧
      (work 9).cells = (wordTape wit).cells := by
  obtain ⟨source,prior,hsource,_,k,l,b,wt,hmeaning,_,hc,hwork,hout⟩ := h
  have hb : b = true ∧ prior = true := by
    simpa only [↓reduceIte,Bool.and_eq_true] using (VerifierDimensionData.one_injective hout).symm
  obtain ⟨hb,hprior⟩ := hb
  subst b; subst prior
  obtain ⟨w',he,hk,hl⟩ := hmeaning.2.2 rfl
  have hww := congrArg BinaryWitnessData.decode he
  rw [BinaryWitnessData.decode_encode,hw] at hww
  have hw' := Option.some.inj hww
  subst w'
  subst k; subst l
  obtain ⟨p,hp,_,haccepted⟩ := hsource.1
  have hp' : p = true := (VerifierDimensionData.one_injective hp).symm
  subst p
  obtain ⟨q,m,n,ns,_,hsrc,_,_,_,hi,hslots⟩ := haccepted rfl
  have hencode := BinarySourceData.decode_reencode hs
  have hwire : VerifierSourceGrammar.wire (m::n::ns) =
      VerifierSourceGrammar.wire (s.entities::s.reactions::s.values) := hsrc.trans hencode.symm
  have hlist := VerifierSourcePositive.wire_injective hwire
  simp only [List.cons.injEq] at hlist
  obtain ⟨rfl,rfl,rfl⟩ := hlist
  refine ⟨hi,?_,?_,?_⟩
  · rw [hwork,hslots]; exact VerifierCountPrepare.unary_eq_reg _
  · rw [hwork,hslots]; exact VerifierCountPrepare.unary_eq_reg _
  · rw [hwork]; exact hc

theorem dimension_slots (x₁ y₁ x₂ y₂ : List Bool) (v : Bool) (inp₀ : Tape) (base : Fin 11 → Tape)
    {inp : Tape} {work : Fin 11 → Tape} {out : Tape}
    (h : VerifierDimensionCompare.bothAfter x₁ y₁ x₂ y₂ v inp₀ base inp work out)
    (j : Fin 11) (hj : j = 5 ∨ j = 8 ∨ j = 9) : work j = base j := by
  obtain ⟨mid,⟨_,a,b,_,_,_,_,hmid,_⟩,_,c,d,_,_,_,_,hwork,_⟩ := h
  rcases hj with rfl | rfl | rfl
  all_goals rw [hwork,hmid]; rfl

theorem dimensions_frame (src wit : List Bool) (s : BinarySourceData.DenseSource)
    (w : BinaryWitnessData.Witness)
    (hs : BinarySourceData.decode src = some s) (hw : BinaryWitnessData.decode wit = some w)
    {inp : Tape} {work : Fin 11 → Tape}
    (h : VerifierRawDimensions.after src wit inp work (one .start true)) :
    inp.HasBinarySuffix (BinaryFields.encode (s.values.map Nat.bits)) ∧
      work 5 = regTape w.mask.length ∧ work 8 = regTape w.flow.length ∧
      (work 9).cells = (wordTape wit).cells := by
  rcases h with ⟨_,hbad⟩ | ⟨base,a,b,k,l,hprep,_,hcomp⟩
  · have hf := VerifierDimensionData.one_injective hbad; cases hf
  · obtain ⟨hi,h5,h8,h9⟩ := prepared_frame src wit s w hs hw hprep
    have hp := dimension_slots _ _ _ _ _ _ _ hcomp
    exact ⟨hi,(hp 5 (by simp)).trans h5,(hp 8 (by simp)).trans h8,
      (congrArg Tape.cells (hp 9 (by simp))).trans h9⟩

/-- Recover the physical facts needed by the kernel initializer from actual
accepted validation, retaining the witness cursor rather than assuming head one. -/
theorem accepted_frame (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape}
    (h : VerifierRawCardinality.after src wit inp work (one .start true)) :
    ∃ s : BinarySourceData.DenseSource, ∃ w : BinaryWitnessData.Witness,
      BinarySourceData.decode src = some s ∧ BinaryWitnessData.decode wit = some w ∧
      w.encode = wit ∧ 0 < s.entities ∧ 0 < s.reactions ∧
      s.entities = w.mask.length ∧ s.reactions = w.flow.length ∧ s.WellFormed ∧
      inp.HasBinarySuffix (BinaryFields.encode (s.values.map Nat.bits)) ∧
      work 5 = regTape s.entities ∧ work 8 = regTape s.reactions ∧
      (work 9).cells = (wordTape wit).cells ∧ ∀ j, Parked (work j) := by
  obtain ⟨s,w,hs,hw,hm,hn,hem,hrn,hwf,he⟩ := VerifierTypedRecovery.accepted_decode src wit h
  rcases h with ⟨_,hbad⟩ | ⟨base,q,m,n,hprep,_,hcheck⟩
  · have hf := VerifierDimensionData.one_injective hbad; cases hf
  · obtain ⟨hi,h5,h8,h9⟩ := dimensions_frame src wit s w hs hw hprep
    obtain ⟨_,hpark,_⟩ := VerifierCardinalityData.parked src wit hprep
    obtain ⟨_,a,b,ha,hb,_,_,hwork,_⟩ := hcheck
    refine ⟨s,w,hs,hw,he,hm,hn,hem,hrn,hwf,hi,?_,?_,?_,?_⟩
    · rw [hwork]
      simpa [VerifierFieldCardinalityCheck.changed,VerifierFieldCardinality.cleared,
        VerifierFieldCardinalityCount.frame,hem] using h5
    · rw [hwork]
      simpa [VerifierFieldCardinalityCheck.changed,VerifierFieldCardinality.cleared,
        VerifierFieldCardinalityCount.frame,hrn] using h8
    · rw [hwork]; exact h9
    · rw [hwork]
      intro j
      fin_cases j
      · exact ⟨ha.1,ha.2.2.2⟩
      · exact hpark 1
      · exact hpark 2
      · exact hpark 3
      · exact parked_regTape 0
      · exact hpark 5
      · exact hpark 6
      · exact hpark 7
      · exact hpark 8
      · exact hpark 9
      · exact ⟨hb.1,hb.2.2.2⟩

end UnconstrainedPACDetection.VerifierRawFrame

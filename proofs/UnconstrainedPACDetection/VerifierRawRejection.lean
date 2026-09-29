module

public import proofs.UnconstrainedPACDetection.VerifierRawFrame
public import proofs.UnconstrainedPACDetection.BinaryIntegerVerifier

@[expose] public section

namespace UnconstrainedPACDetection.VerifierRawRejection
open Complexity Complexity.TM
open VerifierVerdictAnd (one)
open VerifierTypedRecovery (word_injective reg_injective)

theorem joint_accept (src wit : List Bool) (s : BinarySourceData.DenseSource)
    (w : BinaryWitnessData.Witness) (hs : BinarySourceData.decode src = some s)
    (hm : 0 < s.entities) (hn : 0 < s.reactions) (he : w.encode = wit)
    {inp : Tape} {work : Fin 11 → Tape} {out : Tape}
    (h : VerifierJointPrepare.after src wit inp work out) : out = one .start true := by
  obtain ⟨source,prior,hsource,_,k,l,b,wt,hmeaning,_,_,_,hout⟩ := h
  have hdim : VerifierSourceHeaders.HasDimensions src :=
    ⟨s.entities,s.reactions,s.values,BinarySourceData.decode_reencode hs,hm,hn⟩
  obtain ⟨p,hp,hiff,_⟩ := hsource.1
  have hp' : p = true := hiff.mpr hdim
  subst p
  have hprior := VerifierDimensionData.one_injective hp
  have hb : b = true := hmeaning.2.1.mpr ⟨w,he⟩
  simpa only [hprior,hb,ite_true,Bool.true_and] using hout

theorem operands_correct (src wit : List Bool) (s : BinarySourceData.DenseSource)
    (w : BinaryWitnessData.Witness) (hs : BinarySourceData.decode src = some s)
    (hw : BinaryWitnessData.decode wit = some w)
    {inp : Tape} {base : Fin 11 → Tape} {a b k l : Nat}
    (hprep : VerifierJointPrepare.after src wit inp base (one .start true))
    (hparams : VerifierDimensionData.Operands src wit base a b k l) :
    a = s.entities ∧ b = s.reactions ∧ k = w.mask.length ∧ l = w.flow.length := by
  obtain ⟨q,m,n,ns,w',he,_,_,_,hwit,_,h1,h2,h3,h6,_,_⟩ :=
    VerifierTypedRecovery.prepared_data src wit hprep
  have hwire : VerifierSourceGrammar.wire (m::n::ns) =
      VerifierSourceGrammar.wire (s.entities::s.reactions::s.values) :=
    he.trans (BinarySourceData.decode_reencode hs).symm
  have hlist := VerifierSourcePositive.wire_injective hwire
  simp only [List.cons.injEq] at hlist
  obtain ⟨rfl,rfl,rfl⟩ := hlist
  have hww := congrArg BinaryWitnessData.decode hwit
  rw [BinaryWitnessData.decode_encode,hw] at hww
  have hw' := Option.some.inj hww
  subst w'
  obtain ⟨_,_,_,ha,hb,hk,hl,_⟩ := hparams
  refine ⟨?_,?_,?_,?_⟩
  · simpa using congrArg BinaryFields.readNat (word_injective (ha.symm.trans h1))
  · simpa using congrArg BinaryFields.readNat (word_injective (hb.symm.trans h2))
  · simpa only [VerifierUnaryBinary.digits_value] using
      congrArg BinaryFields.readNat (word_injective (hk.symm.trans h3))
  · simpa only [VerifierUnaryBinary.digits_value] using
      congrArg BinaryFields.readNat (word_injective (hl.symm.trans h6))

theorem dimensions_accept (src wit : List Bool) (s : BinarySourceData.DenseSource)
    (w : BinaryWitnessData.Witness) (hs : BinarySourceData.decode src = some s)
    (hw : BinaryWitnessData.decode wit = some w) (hm : 0 < s.entities) (hn : 0 < s.reactions)
    (hem : s.entities = w.mask.length) (hrn : s.reactions = w.flow.length) (he : w.encode = wit)
    {inp : Tape} {work : Fin 11 → Tape} {out : Tape}
    (h : VerifierRawDimensions.after src wit inp work out) : out = one .start true := by
  rcases h with ⟨hprep,_⟩ | ⟨base,a,b,k,l,hprep,hparams,hcomp⟩
  · have hf := VerifierDimensionData.one_injective (joint_accept src wit s w hs hm hn he hprep)
    cases hf
  · obtain ⟨ha,hb,hk,hl⟩ := operands_correct src wit s w hs hw hprep hparams
    obtain ⟨v,hout,hiff⟩ := VerifierDimensionCompare.numeric_verdict a b k l true inp base hcomp
    have hv : v = true := hiff.mpr ⟨ha.trans (hem.trans hk.symm),hb.trans (hrn.trans hl.symm),rfl⟩
    simpa only [hv] using hout

theorem cardinality_accept (src wit : List Bool) (s : BinarySourceData.DenseSource)
    (w : BinaryWitnessData.Witness) (hs : BinarySourceData.decode src = some s)
    (hw : BinaryWitnessData.decode wit = some w) (hm : 0 < s.entities) (hn : 0 < s.reactions)
    (hem : s.entities = w.mask.length) (hrn : s.reactions = w.flow.length) (he : w.encode = wit)
    {inp : Tape} {work : Fin 11 → Tape} {out : Tape}
    (h : VerifierRawCardinality.after src wit inp work out) : out = one .start true := by
  rcases h with ⟨hprep,_⟩ | ⟨base,q,m,n,hprep,hregs,hcheck⟩
  · have hf := VerifierDimensionData.one_injective
      (dimensions_accept src wit s w hs hw hm hn hem hrn he hprep)
    cases hf
  · obtain ⟨q',m',n',ns,w',hsrc,hlen,_,_,_,_,_,h0,h5,h8⟩ :=
      VerifierTypedRecovery.dimensions_data src wit hprep
    obtain ⟨_,_,hq,_,hrm,hrn',_⟩ := hregs
    have hqq := reg_injective (hq.symm.trans h0)
    have hmm := reg_injective (hrm.symm.trans h5)
    have hnn := reg_injective (hrn'.symm.trans h8)
    have hwire : VerifierSourceGrammar.wire (m'::n'::ns) =
        VerifierSourceGrammar.wire (s.entities::s.reactions::s.values) :=
      hsrc.trans (BinarySourceData.decode_reencode hs).symm
    have hlist := VerifierSourcePositive.wire_injective hwire
    simp only [List.cons.injEq] at hlist
    obtain ⟨hm',hn',hns⟩ := hlist
    have hwf := BinarySourceData.decode_wellFormed hs
    change s.values.length = 2*(s.entities*s.reactions) at hwf
    have hcard : q = 2*m*n+2 := by
      simp only [List.length_cons] at hlen
      rw [← hqq,hns] at hlen
      rw [hmm,hnn,hm',hn']
      nlinarith
    obtain ⟨v,hout,hiff⟩ := VerifierFieldCardinalityCheck.numeric_verdict q (2*m*n+2) true inp _ hcheck
    have hv : v = true := hiff.mpr ⟨hcard,rfl⟩
    simpa only [hv] using hout

/-- Every rejection by raw validation is a rejection by the actual total
verifier, including malformed encodings and dimension/cardinality mismatches. -/
theorem rejected_verifier (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape}
    (h : VerifierRawCardinality.after src wit inp work (one .start false)) :
    BinaryIntegerVerifier.verify src wit = false := by
  cases hv : BinaryIntegerVerifier.verify src wit with
  | false => rfl
  | true =>
    unfold BinaryIntegerVerifier.verify at hv
    cases hs : BinarySourceData.decode src with
    | none => simp [hs] at hv
    | some s =>
      simp only [hs] at hv
      by_cases hz : s.entities = 0 ∨ s.reactions = 0
      · simp [hz] at hv
      · rw [ite_eq_right hz] at hv
        cases hw : BinaryWitnessData.decode wit with
        | none => simp [hw] at hv
        | some w =>
          simp only [hw] at hv
          by_cases hshape : w.mask.length = s.entities ∧ w.flow.length = s.reactions ∧ w.encode = wit
          · have hf := cardinality_accept src wit s w hs hw (by omega) (by omega)
              hshape.1.symm hshape.2.1.symm hshape.2.2 h
            have hfalse := VerifierDimensionData.one_injective hf
            cases hfalse
          · simp [hshape] at hv

end UnconstrainedPACDetection.VerifierRawRejection

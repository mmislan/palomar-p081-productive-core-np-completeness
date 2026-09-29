module

public import proofs.UnconstrainedPACDetection.VerifierRawCardinality
public import proofs.UnconstrainedPACDetection.BinarySourceData
public import proofs.UnconstrainedPACDetection.BinaryPACVerifier

@[expose] public section

namespace UnconstrainedPACDetection.VerifierTypedRecovery
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)

theorem word_injective {xs ys : List Bool} (h : wordTape xs = wordTape ys) : xs = ys := by
  have hx := Tape.init_move_right_hasBinaryString xs
  have hy := Tape.init_move_right_hasBinaryString ys
  change (wordTape xs).HasBinaryString xs at hx
  change (wordTape ys).HasBinaryString ys at hy
  rw [← h] at hy
  have hlen : xs.length = ys.length := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hl | hl
    · have he := hy.2.1 xs.length hl
      rw [hx.2.2 xs.length le_rfl] at he
      cases hb : ys[xs.length] <;> simp [hb, Γ.ofBool] at he
    · have he := hx.2.1 ys.length hl
      rw [hy.2.2 ys.length le_rfl] at he
      cases hb : xs[ys.length] <;> simp [hb, Γ.ofBool] at he
  apply List.ext_getElem hlen
  intro i hi hj
  have he := (hx.2.1 i hi).symm.trans (hy.2.1 i hj)
  cases hb : xs[i] <;> cases hc : ys[i] <;> simp_all [Γ.ofBool]

theorem reg_injective {m n : Nat} (h : regTape m = regTape n) : m = n := by
  rw [← VerifierCountPrepare.unary_eq_reg, ← VerifierCountPrepare.unary_eq_reg] at h
  have he := congrArg List.length (word_injective h)
  simpa using he

/-- Retain the full encoding relation together with the registers that its consumer reads. -/
theorem prepared_data (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape}
    (h : VerifierJointPrepare.after src wit inp work (one .start true)) :
    ∃ q m n ns, ∃ w : BinaryWitnessData.Witness,
      VerifierSourceGrammar.wire (m::n::ns) = src ∧ (m::n::ns).length = q ∧
      0 < m ∧ 0 < n ∧ w.encode = wit ∧
      work 0 = regTape q ∧ work 1 = wordTape m.bits ∧ work 2 = wordTape n.bits ∧
      work 3 = wordTape (VerifierUnaryBinary.digits w.mask.length) ∧
      work 6 = wordTape (VerifierUnaryBinary.digits w.flow.length) ∧
      work 5 = regTape w.mask.length ∧ work 8 = regTape w.flow.length := by
  obtain ⟨source,prior,hsource,_,k,l,b,wt,hmeaning,_,_,hw,ho⟩ := h
  have hb : b = true ∧ prior = true := by
    simpa only [↓reduceIte,Bool.and_eq_true] using (VerifierDimensionData.one_injective ho).symm
  obtain ⟨hb,hprior⟩ := hb
  subst b; subst prior
  obtain ⟨w,he,hk,hl⟩ := hmeaning.2.2 rfl
  subst k; subst l
  obtain ⟨p,hp,_,haccepted⟩ := hsource.1
  have hp' : p = true := (VerifierDimensionData.one_injective hp).symm
  subst p
  obtain ⟨q,m,n,ns,_,hs,hlen,hm,hn,_,hslots⟩ := haccepted rfl
  refine ⟨q,m,n,ns,w,hs,hlen,hm,hn,he,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals rw [hw,hslots]
  · exact VerifierCountPrepare.unary_eq_reg q
  · rfl
  · rfl
  · rfl
  · rfl
  · exact VerifierCountPrepare.unary_eq_reg _
  · exact VerifierCountPrepare.unary_eq_reg _

theorem dimensions_data (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape}
    (h : VerifierRawDimensions.after src wit inp work (one .start true)) :
    ∃ q m n ns, ∃ w : BinaryWitnessData.Witness,
      VerifierSourceGrammar.wire (m::n::ns) = src ∧ (m::n::ns).length = q ∧
      0 < m ∧ 0 < n ∧ w.encode = wit ∧ m = w.mask.length ∧ n = w.flow.length ∧
      work 0 = regTape q ∧ work 5 = regTape m ∧ work 8 = regTape n := by
  rcases h with ⟨_,hbad⟩ | ⟨base,a,b,k,l,hprep,hparams,hcomp⟩
  · have hf := VerifierDimensionData.one_injective hbad
    cases hf
  · obtain ⟨v,hv,hiff⟩ := VerifierDimensionCompare.numeric_verdict a b k l true inp base hcomp
    have hv' : v = true := (VerifierDimensionData.one_injective hv).symm
    obtain ⟨hak,hbl,_⟩ := hiff.mp hv'
    obtain ⟨q,m,n,ns,w,he,hlen,hm,hn,hwit,h0,h1,h2,h3,h6,h5,h8⟩ := prepared_data src wit hprep
    obtain ⟨_,_,_,ha,hb,hk,hl,_⟩ := hparams
    have ham : a = m := by
      simpa using congrArg BinaryFields.readNat (word_injective (ha.symm.trans h1))
    have hbn : b = n := by
      simpa using congrArg BinaryFields.readNat (word_injective (hb.symm.trans h2))
    have hkm : k = w.mask.length := by
      simpa only [VerifierUnaryBinary.digits_value] using
        congrArg BinaryFields.readNat (word_injective (hk.symm.trans h3))
    have hln : l = w.flow.length := by
      simpa only [VerifierUnaryBinary.digits_value] using
        congrArg BinaryFields.readNat (word_injective (hl.symm.trans h6))
    have hmw : m = w.mask.length := ham.symm.trans (hak.trans hkm)
    have hnw : n = w.flow.length := hbn.symm.trans (hbl.trans hln)
    have hp := VerifierCardinalityData.preserved_slots _ _ _ _ _ _ _ hcomp
    refine ⟨q,m,n,ns,w,he,hlen,hm,hn,hwit,hmw,hnw,?_,?_,?_⟩
    · exact (hp 0 (by simp)).trans h0
    · simpa only [hmw] using (hp 5 (by simp)).trans h5
    · simpa only [hnw] using (hp 8 (by simp)).trans h8

/-- An accepting raw validator really determines a canonical typed source and
witness; no decode assumption or dimension supplied as advice is used. -/
theorem accepted_decode (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape}
    (h : VerifierRawCardinality.after src wit inp work (one .start true)) :
    ∃ s : BinarySourceData.DenseSource, ∃ w : BinaryWitnessData.Witness,
      BinarySourceData.decode src = some s ∧ BinaryWitnessData.decode wit = some w ∧
      0 < s.entities ∧ 0 < s.reactions ∧
      s.entities = w.mask.length ∧ s.reactions = w.flow.length ∧
      s.WellFormed ∧ w.encode = wit := by
  obtain ⟨base,q,m,n,hprep,hregs,hcard⟩ := VerifierRawCardinality.accepted_cardinality src wit h
  obtain ⟨q',m',n',ns,w,he,hlen,hm,hn,hwit,hmw,hnw,h0,h5,h8⟩ := dimensions_data src wit hprep
  obtain ⟨_,_,hq,_,hrm,hrn,_⟩ := hregs
  have hqq := reg_injective (hq.symm.trans h0)
  have hmm := reg_injective (hrm.symm.trans h5)
  have hnn := reg_injective (hrn.symm.trans h8)
  simp only [← hqq, ← hmm, ← hnn] at he hlen hm hn hmw hnw
  let s : BinarySourceData.DenseSource := ⟨m,n,ns⟩
  have hlen' : ns.length = 2*(m*n) := by
    simp only [List.length_cons] at hlen
    nlinarith [hcard]
  have hs : s.WellFormed := hlen'
  have hencode : s.encode = src := he
  refine ⟨s,w,?_,?_,hm,hn,hmw,hnw,hs,hwit⟩
  · rw [← hencode]
    exact BinarySourceData.decode_encode s hs
  · rw [← hwit]
    exact BinaryWitnessData.decode_encode w

theorem table_split (s : BinarySourceData.DenseSource) (hs : s.WellFormed) :
    (s.values.take (s.entities*s.reactions)).length = s.entities*s.reactions ∧
    (s.values.drop (s.entities*s.reactions)).length = s.entities*s.reactions ∧
    s.values.take (s.entities*s.reactions) ++ s.values.drop (s.entities*s.reactions) = s.values := by
  have hlen := hs
  change s.values.length = 2*(s.entities*s.reactions) at hlen
  refine ⟨?_,?_,List.take_append_drop _ _⟩
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega

/-- Consume raw acceptance in the existing verifier, including its bounded-flow
predicate. This does not assert that raw validation already checks productivity. -/
theorem accepted_verifier (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape}
    (h : VerifierRawCardinality.after src wit inp work (one .start true)) :
    ∃ s : BinarySourceData.DenseSource, ∃ w : BinaryWitnessData.Witness,
      BinarySourceData.decode src = some s ∧ BinaryWitnessData.decode wit = some w ∧
      s.WellFormed ∧ w.encode = wit ∧
      (s.values.take (s.entities*s.reactions)).length = s.entities*s.reactions ∧
      (s.values.drop (s.entities*s.reactions)).length = s.entities*s.reactions ∧
      s.values.take (s.entities*s.reactions) ++ s.values.drop (s.entities*s.reactions) = s.values ∧
      BinaryPACVerifier.verify src wit =
        s.toSource.checkBoundedFlow (w.entities s.entities) (w.values s.reactions) := by
  obtain ⟨s,w,hs,hw,hm,hn,hem,hrn,hwf,he⟩ := accepted_decode src wit h
  obtain ⟨hl,hr,ht⟩ := table_split s hwf
  refine ⟨s,w,hs,hw,hwf,he,hl,hr,ht,?_⟩
  have hnonzero : ¬(s.entities = 0 ∨ s.reactions = 0) := by omega
  simp only [BinaryPACVerifier.verify,hs,ite_eq_right hnonzero,hw]
  rw [ite_eq_left ⟨hem.symm,hrn.symm,he⟩]

end UnconstrainedPACDetection.VerifierTypedRecovery

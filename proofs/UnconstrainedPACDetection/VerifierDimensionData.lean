module

public import proofs.UnconstrainedPACDetection.VerifierJointPrepare

@[expose] public section

namespace UnconstrainedPACDetection.VerifierDimensionData
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)

theorem one_injective {a b : Bool} (h : one .start a = one .start b) : a = b := by
  have hc : Γ.ofBool a = Γ.ofBool b := congrArg (fun t : Tape => t.cells 1) h
  cases a <;> cases b <;> first | rfl | cases hc

theorem parked (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape} {out : Tape}
    (h : VerifierJointPrepare.after src wit inp work out) :
    Parked inp ∧ (∀ j, Parked (work j)) ∧ ∃ v, out = one .start v := by
  obtain ⟨source,prior,hsource,_,k,l,b,wt,_,hwt,_,hw,ho⟩ := h
  refine ⟨hsource.2.1,?_,_,ho⟩
  rw [hw]; intro j; fin_cases j
  · exact hsource.2.2 0
  · exact hsource.2.2 1
  · exact hsource.2.2 2
  · exact VerifierCountPrepare.pair_parked k l true true 0
  · exact VerifierCountPrepare.pair_parked k l true true 1
  · exact VerifierCountPrepare.pair_parked k l true true 2
  · exact VerifierCountPrepare.pair_parked k l true true 3
  · exact VerifierCountPrepare.pair_parked k l true true 4
  · exact VerifierCountPrepare.pair_parked k l true true 5
  · exact hwt
  · exact VerifierReactionLoop.word_parked []

def Operands (src wit : List Bool) (work : Fin 11 → Tape) (m n k l : ℕ) : Prop :=
  k+l ≤ wit.length ∧ m.bits.length ≤ src.length ∧ n.bits.length ≤ src.length ∧
  work 1 = wordTape m.bits ∧ work 2 = wordTape n.bits ∧
  work 3 = wordTape (VerifierUnaryBinary.digits k) ∧
  work 6 = wordTape (VerifierUnaryBinary.digits l) ∧ work 10 = wordTape []

theorem accepted_operands (src wit : List Bool) {inp : Tape} {work : Fin 11 → Tape}
    (h : VerifierJointPrepare.after src wit inp work (one .start true)) :
    ∃ m n k l, Operands src wit work m n k l := by
  obtain ⟨source,prior,hsource,_,k,l,b,wt,hmeaning,_,_,hw,ho⟩ := h
  have hb : b = true ∧ prior = true := by
    simpa only [↓reduceIte,Bool.and_eq_true] using (one_injective ho).symm
  obtain ⟨hb,hprior⟩ := hb
  subst b; subst prior
  obtain ⟨p,hp,_,haccepted⟩ := hsource.1
  have hp' : p = true := (one_injective hp).symm
  subst p
  obtain ⟨count,m,n,ns,_,he,_,_,_,_,hs⟩ := haccepted rfl
  have hlen := congrArg List.length he
  change (BinaryFields.encodeField m.bits ++ (BinaryFields.encodeField n.bits ++
    VerifierSourceGrammar.wire ns)).length = src.length at hlen
  simp only [List.length_append,BinaryFields.encodeField_length] at hlen
  refine ⟨m,n,k,l,hmeaning.1,by omega,by omega,?_,?_,?_,?_,?_⟩
  all_goals rw [hw,hs]; rfl

theorem comparison_bound (src wit : List Bool) (work : Fin 11 → Tape) (m n k l : ℕ)
    (h : Operands src wit work m n k l) :
    max m.bits.length (VerifierUnaryBinary.digits k).length +
      max n.bits.length (VerifierUnaryBinary.digits l).length + 11 ≤
      2*src.length+2*wit.length+13 := by
  have hk := VerifierUnaryBinary.digits_length k
  have hl := VerifierUnaryBinary.digits_length l
  have hm := h.2.1
  have hn := h.2.2.1
  have hkl := h.1
  omega

end UnconstrainedPACDetection.VerifierDimensionData

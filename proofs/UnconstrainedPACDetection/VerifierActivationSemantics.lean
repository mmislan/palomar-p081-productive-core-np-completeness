module

public import proofs.UnconstrainedPACDetection.VerifierActivationSide

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationSemantics

theorem hit_iff (es : List (List Bool × Bool)) (a : Bool) :
    VerifierActivationSide.hit es a = true ↔
      a = true ∨ ∃ e ∈ es, e.2 = true ∧ e.1 ≠ [] := by
  induction es generalizing a with
  | nil => simp [VerifierActivationSide.hit]
  | cons e es ih =>
    change VerifierActivationSide.hit es (a || (e.2 && !e.1.isEmpty)) = true ↔ _
    rw [ih]
    simp only [Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',List.isEmpty_eq_false_iff,
      List.mem_cons,exists_eq_or_imp]
    tauto

theorem bits_nonempty (n : ℕ) : n.bits ≠ [] ↔ 0 < n := by
  constructor
  · intro h; by_contra hn; have hz : n = 0 := by omega
    subst n; exact h rfl
  · intro h he
    have hn := BinaryFields.readNat_bits n
    rw [he] at hn
    change 0 = n at hn
    omega

def entries (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (rightSide : Bool) (r : Fin s.reactions) : List (List Bool × Bool) :=
  (List.finRange s.entities).map (fun x =>
    ((VerifierCanonicalCoordinates.coefficient s rightSide r x).bits,w.mask.getD x.val false))

def verdict (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (rightSide : Bool) (r : Fin s.reactions) : Bool :=
  VerifierActivationSide.hit (entries s w rightSide r) false

theorem verdict_iff (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (rightSide : Bool) (r : Fin s.reactions) :
    verdict s w rightSide r = true ↔
      ∃ x ∈ w.entities s.entities, 0 < VerifierCanonicalCoordinates.coefficient s rightSide r x := by
  simp only [verdict,hit_iff,Bool.false_eq_true,false_or,entries,List.mem_map]
  constructor
  · rintro ⟨e,⟨x,hx,rfl⟩,hm,hp⟩
    exact ⟨x,by simpa [BinaryWitnessData.Witness.entities] using hm,bits_nonempty _ |>.mp hp⟩
  · rintro ⟨x,hx,hp⟩
    refine ⟨_,⟨x,List.mem_finRange x,rfl⟩,?_,(bits_nonempty _).mpr hp⟩
    simpa [BinaryWitnessData.Witness.entities] using hx

theorem sideAdmissible_iff (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (r : Fin s.reactions) :
    s.toSource.sideAdmissible (w.entities s.entities) r ↔
      verdict s w false r = true ∧ verdict s w true r = true := by
  simp only [verdict_iff,ReversibleSource.sideAdmissible,VerifierCanonicalCoordinates.coefficient,
    Bool.false_eq_true,↓reduceIte]

theorem integerFlowChecks_iff (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (w : BinaryWitnessData.Witness) :
    s.toSource.IntegerFlowChecks (w.entities s.entities) (w.values s.reactions) ↔
      (w.entities s.entities).Nonempty ∧
      (∀ r, w.values s.reactions r ≠ 0 →
        verdict s w false r = true ∧ verdict s w true r = true) ∧
      VerifierEntityOuterLoop.accumulator s hn w true s.entities = true := by
  rw [VerifierEntityOuterSemantics.integerFlowChecks_iff s hn w]
  simp_rw [sideAdmissible_iff]

end UnconstrainedPACDetection.VerifierActivationSemantics

module

public import proofs.IrrRAFEnumeration.SATSource

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open RAF SATCompletion CircuitSource

def decodeInputs {n : Nat} (U : Finset (Fin (Fintype.card (Choice n)))) :=
  U.image (inputCode n).symm

@[simp] theorem encode_decode {n : Nat} (U : Finset (Fin (Fintype.card (Choice n)))) :
    encodeInputs (decodeInputs U) = U := by
  simp [encodeInputs, decodeInputs, Finset.image_image]

@[simp] theorem decode_encode {n : Nat} (T : Finset (Choice n)) :
    decodeInputs (encodeInputs T) = T := by
  simp [encodeInputs, decodeInputs, Finset.image_image]

@[simp] theorem encode_subset_iff {n : Nat} (T U : Finset (Choice n)) :
    encodeInputs T ⊆ encodeInputs U ↔ T ⊆ U :=
  Finset.image_subset_image_iff (inputCode n).injective

def sourceSet {n m : Nat} (T : Finset (Choice n)) :
    Finset (Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))) :=
  canonical (encodeInputs T)

theorem sourceSet_injective {n m : Nat} :
    Function.Injective (sourceSet (m := m) : Finset (Choice n) → _) := by
  intro T U h
  have he := canonical_injective h
  have hd := congrArg decodeInputs he
  simpa using hd

theorem minimal_accepts_encode_iff {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (T : Finset (Choice n)) :
    Minimal (Accepts (rules Φ)) (encodeInputs T) ↔ Minimal (eval (family Φ)) T := by
  constructor
  · intro h
    refine ⟨(accepts_encode_iff_eval Φ T).mp h.1, ?_⟩
    intro U hU hUT
    exact (encode_subset_iff T U).mp
      (h.2 ((accepts_encode_iff_eval Φ U).mpr hU) ((encode_subset_iff U T).mpr hUT))
  · intro h
    refine ⟨(accepts_encode_iff_eval Φ T).mpr h.1, ?_⟩
    intro U hU hUT
    have hdec : eval (family Φ) (decodeInputs U) := by
      apply (accepts_encode_iff_eval Φ _).mp
      simpa using hU
    have hsub : decodeInputs U ⊆ T := by
      apply (encode_subset_iff _ _).mp
      simpa using hUT
    have hrev := (encode_subset_iff T (decodeInputs U)).mpr (h.2 hdec hsub)
    simpa using hrev

theorem sourceSet_irreducible_iff {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (T : Finset (Choice n)) :
    MinRAFApprox.SetCoverSource.IsIrreducibleRAF (crs (rules Φ)) catalysis (sourceSet T) ↔
      Minimal (eval (family Φ)) T := by
  rw [sourceSet, canonical_irreducible_iff, minimal_accepts_encode_iff]

theorem irreducible_iff_exists_sourceSet {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (S : Finset (Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)))) :
    MinRAFApprox.SetCoverSource.IsIrreducibleRAF (crs (rules Φ)) catalysis S ↔
      ∃ T, Minimal (eval (family Φ)) T ∧ S = sourceSet T := by
  constructor
  · intro hS
    obtain ⟨U, _, heq⟩ := (isRAF_iff_exists_canonical (rules Φ) S).mp hS.1
    have heq' : S = sourceSet (decodeInputs U) := by simpa [sourceSet] using heq
    refine ⟨decodeInputs U, ?_, heq'⟩
    apply (sourceSet_irreducible_iff Φ _).mp
    rw [← heq']
    exact hS
  · rintro ⟨T, hT, rfl⟩
    exact (sourceSet_irreducible_iff Φ T).mpr hT

/-- Literal CRS completeness iff UNSAT, for a polynomially described known
family of genuine irrRAFs. The source evaluation is proved, not a premise. -/
theorem literal_baseline_complete_iff_unsat {n m : Nat} (hn : 2 ≤ n)
    (Φ : Fin m → Finset (Choice n)) :
    (∀ S, MinRAFApprox.SetCoverSource.IsIrreducibleRAF (crs (rules Φ)) catalysis S ↔
      ∃ i : Fin n, S = sourceSet (m := m) (pair i)) ↔
      ¬ ∃ T, ¬ conflict T ∧ covers T ∧ hits (family Φ) T := by
  rw [← SATCompletion.baseline_complete_iff_unsat hn (family Φ)]
  constructor
  · intro h T
    constructor
    · intro hT
      obtain ⟨i, hi⟩ := (h (sourceSet T)).mp ((sourceSet_irreducible_iff Φ T).mpr hT)
      exact ⟨i, sourceSet_injective hi⟩
    · rintro ⟨i, rfl⟩
      exact pair_minimal hn (family Φ) i
  · intro h S
    rw [irreducible_iff_exists_sourceSet]
    constructor
    · rintro ⟨T, hT, heq⟩
      obtain ⟨i, rfl⟩ := (h T).mp hT
      exact ⟨i, heq⟩
    · rintro ⟨i, heq⟩
      exact ⟨pair i, (h (pair i)).mpr ⟨i, rfl⟩, heq⟩

end IrrRAFEnumeration.SATSource

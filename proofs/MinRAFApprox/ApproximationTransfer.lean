module

public import proofs.MinRAFApprox.Gadgets.SetCoverCardinality

@[expose] public section

namespace MinRAFApprox

open RAF

/-- `S` is a feasible object of minimum cardinality for predicate `P`. -/
def IsMinimumCard {α : Type*} [DecidableEq α]
    (P : Finset α → Prop) (S : Finset α) : Prop :=
  P S ∧ ∀ T, P T → S.card ≤ T.card

namespace SetCoverSource

variable {m n M : Nat}

/-- Exact optimum correspondence, expressed without choosing an optimizer:
a cover is minimum iff its canonical RAF is minimum. -/
theorem minimumCover_iff_minimumRAF
    (I : SetCoverInstance (Fin m) (Fin n))
    (hm : 0 < m) (hM : 0 < M) (C : Finset (Fin n)) :
    IsMinimumCard I.Covers C ↔
      IsMinimumCard (IsRAF (crs m n M) (catalysis I))
        (canonicalRAF (U := Fin m) (K := Fin M) C) := by
  constructor
  · rintro ⟨hcover, hminimal⟩
    refine ⟨canonical_isRAF I hm hM C hcover, ?_⟩
    intro S hS
    obtain ⟨D, hD, rfl⟩ := (setCoverSource_raf_iff I hm hM S).1 hS
    rw [canonicalRAF_card C, canonicalRAF_card D]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left M (hminimal D hD)) m
  · rintro ⟨hraf, hminimal⟩
    obtain ⟨D, hD, hDC⟩ := (setCoverSource_raf_iff I hm hM
      (canonicalRAF (U := Fin m) (K := Fin M) C)).1 hraf
    have hEq : D = C := by
      ext j
      let k : Fin M := lastFin M hM
      have hDmem : MinRAFApprox.Reaction.block (U := Fin m) j k ∈
          canonicalRAF D ↔ j ∈ D := MinRAFApprox.block_mem_canonicalRAF D j k
      have hCmem : MinRAFApprox.Reaction.block (U := Fin m) j k ∈
          canonicalRAF C ↔ j ∈ C := MinRAFApprox.block_mem_canonicalRAF C j k
      constructor
      · intro hj
        apply hCmem.1
        rw [hDC]
        exact hDmem.2 hj
      · intro hj
        apply hDmem.1
        rw [← hDC]
        exact hCmem.2 hj
    subst D
    have hcover : I.Covers C := hD
    refine ⟨hcover, ?_⟩
    intro D hD
    have hle := hminimal (canonicalRAF (U := Fin m) (K := Fin M) D)
      (canonical_isRAF I hm hM D hD)
    rw [canonicalRAF_card C, canonicalRAF_card D] at hle
    have hmul : M * C.card ≤ M * D.card := Nat.le_of_add_le_add_left hle
    exact Nat.le_of_mul_le_mul_left hmul hM

/-- Arithmetic core of approximation preservation.  When `M ≥ m`, a
`c`-approximate canonical RAF decodes to a `(2c-1)`-approximate cover. -/
theorem approximation_decode_arithmetic
    {c τ k : Nat} (hc : 1 ≤ c) (hτ : 1 ≤ τ)
    (hM : 0 < M) (hamp : m ≤ M)
    (happrox : m + M * k ≤ c * (m + M * τ)) :
    k ≤ (2 * c - 1) * τ := by
  have hcdecomp : c = 1 + (c - 1) := by omega
  have hcm : c * m = m + (c - 1) * m := by
    calc
      c * m = (1 + (c - 1)) * m := by rw [← hcdecomp]
      _ = m + (c - 1) * m := by ring
  have hexpand : c * (m + M * τ) =
      m + ((c - 1) * m + M * (c * τ)) := by
    rw [Nat.mul_add, hcm]
    ring
  rw [hexpand] at happrox
  have hcancel : M * k ≤ (c - 1) * m + M * (c * τ) :=
    Nat.le_of_add_le_add_left happrox
  have hscale : (c - 1) * m ≤ (c - 1) * M :=
    Nat.mul_le_mul_left (c - 1) hamp
  have hmul : M * k ≤ M * (c * τ + (c - 1)) := by
    calc
      M * k ≤ (c - 1) * m + M * (c * τ) := hcancel
      _ ≤ (c - 1) * M + M * (c * τ) :=
        Nat.add_le_add_right hscale (M * (c * τ))
      _ = M * (c * τ + (c - 1)) := by ring
  have hdecoded : k ≤ c * τ + (c - 1) :=
    Nat.le_of_mul_le_mul_left hmul hM
  have hextra : c - 1 ≤ (c - 1) * τ := by
    simpa using Nat.mul_le_mul_left (c - 1) hτ
  calc
    k ≤ c * τ + (c - 1) := hdecoded
    _ ≤ c * τ + (c - 1) * τ := Nat.add_le_add_left hextra (c * τ)
    _ = (c + (c - 1)) * τ := by ring
    _ = (2 * c - 1) * τ := by
      congr 1
      omega

/-- Concrete decoding statement on the literal source. -/
theorem approximation_decode
    (I : SetCoverInstance (Fin m) (Fin n))
    (hm : 0 < m) (hM : 0 < M) (hamp : m ≤ M)
    (Copt C : Finset (Fin n))
    (hopt : IsMinimumCard I.Covers Copt) (hC : I.Covers C)
    {c : Nat} (hc : 1 ≤ c)
    (happrox :
      (canonicalRAF (U := Fin m) (K := Fin M) C).card ≤
        c * (canonicalRAF (U := Fin m) (K := Fin M) Copt).card) :
    I.Covers C ∧ C.card ≤ (2 * c - 1) * Copt.card := by
  refine ⟨hC, ?_⟩
  have hτ : 1 ≤ Copt.card := by
    rcases Copt.eq_empty_or_nonempty with rfl | hne
    · have := hopt.1 ⟨0, hm⟩
      simp at this
    · exact Finset.one_le_card.mpr hne
  rw [canonicalRAF_card C, canonicalRAF_card Copt] at happrox
  exact approximation_decode_arithmetic hc hτ hM hamp happrox

end SetCoverSource

end MinRAFApprox

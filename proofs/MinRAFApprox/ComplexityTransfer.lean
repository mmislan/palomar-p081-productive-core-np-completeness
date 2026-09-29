module

public import proofs.MinRAFApprox.ApproximationTransfer

@[expose] public section

namespace MinRAFApprox

open RAF Reaction

/-- The reaction labels themselves expose the polynomial source-size formula. -/
def reactionEquiv {U J K : Type*} : Reaction U J K ≃ U ⊕ (J × K) where
  toFun
    | gate u => Sum.inl u
    | block j k => Sum.inr (j, k)
  invFun
    | Sum.inl u => gate u
    | Sum.inr jk => block jk.1 jk.2
  left_inv r := by cases r <;> rfl
  right_inv s := by cases s <;> rfl

/-- The amplified instance has `m + nM` reactions. -/
theorem source_reaction_count (m n M : Nat) :
    Fintype.card (Reaction (Fin m) (Fin n) (Fin M)) = m + n * M := by
  rw [Fintype.card_congr (reactionEquiv
    (U := Fin m) (J := Fin n) (K := Fin M))]
  simp

namespace SetCoverSource

variable {m n M : Nat}

/-- Read the chosen sets directly from the final reaction of each block. -/
def extractCover (hM : 0 < M)
    (S : Finset (Reaction (Fin m) (Fin n) (Fin M))) : Finset (Fin n) :=
  Finset.univ.filter fun j => block (U := Fin m) j (lastFin M hM) ∈ S

/-- Literal extraction is exact on every RAF, not merely on optimal RAFs. -/
theorem extractCover_of_raf
    (I : SetCoverInstance (Fin m) (Fin n)) (hm : 0 < m) (hM : 0 < M)
    (S : Finset (Reaction (Fin m) (Fin n) (Fin M)))
    (hS : IsRAF (crs m n M) (catalysis I) S) :
    I.Covers (extractCover hM S) ∧
      S = canonicalRAF (extractCover hM S) := by
  obtain ⟨C, hC, hSC⟩ := (setCoverSource_raf_iff I hm hM S).1 hS
  have hExtract : extractCover hM S = C := by
    ext j
    simp [extractCover, hSC]
  simpa [hExtract] using And.intro hC hSC

/-- Algorithms returning covers for finite indexed SET COVER instances. -/
abbrev CoverAlgorithm :=
  ∀ m n : Nat, SetCoverInstance (Fin m) (Fin n) → Finset (Fin n)

/-- Algorithms returning reaction subsets on the amplified source family. -/
abbrev SourceRAFAlgorithm :=
  ∀ m n M : Nat, SetCoverInstance (Fin m) (Fin n) →
    Finset (Reaction (Fin m) (Fin n) (Fin M))

/-- A factor-`c` solution approximation for nonempty-universe SET COVER. -/
def IsCoverApprox (c : Nat) (A : CoverAlgorithm) : Prop :=
  ∀ (m n : Nat) (I : SetCoverInstance (Fin m) (Fin n))
    (_hm : 0 < m) (Copt : Finset (Fin n)),
    IsMinimumCard I.Covers Copt →
      I.Covers (A m n I) ∧ (A m n I).card ≤ c * Copt.card

/-- A factor-`c` solution approximation restricted to the literal amplified
MIN-RAF sources.  The benchmark optimum is canonical by the exact theorem. -/
def IsSourceRAFApprox (c : Nat) (A : SourceRAFAlgorithm) : Prop :=
  ∀ (m n M : Nat) (I : SetCoverInstance (Fin m) (Fin n))
    (_hm : 0 < m) (_hM : 0 < M) (Copt : Finset (Fin n)),
    IsMinimumCard I.Covers Copt →
      IsRAF (crs m n M) (catalysis I) (A m n M I) ∧
        (A m n M I).card ≤
          c * (canonicalRAF (U := Fin m) (K := Fin M) Copt).card

/-- The block length used by the polynomial reduction. -/
def amplification (m : Nat) : Nat := max 2 m

theorem amplification_pos (m : Nat) : 0 < amplification m :=
  Nat.lt_of_lt_of_le Nat.zero_lt_two (Nat.le_max_left 2 m)

theorem le_amplification (m : Nat) : m ≤ amplification m := by
  simp [amplification]

/-- Compose a source-family RAF algorithm with the explicit block extractor. -/
def inducedCover (A : SourceRAFAlgorithm) : CoverAlgorithm :=
  fun m n I => extractCover (amplification_pos m) (A m n (amplification m) I)

/-- Approximation-preserving reduction: factor `c` on MIN-RAF gives factor
`2c-1` on SET COVER. -/
theorem sourceRAF_approx_implies_cover_approx
    {c : Nat} (hc : 1 ≤ c) (A : SourceRAFAlgorithm)
    (hA : IsSourceRAFApprox c A) :
    IsCoverApprox (2 * c - 1) (inducedCover A) := by
  intro m n I hm Copt hopt
  let M := amplification m
  have hM : 0 < M := amplification_pos m
  have hamp : m ≤ M := le_amplification m
  obtain ⟨hraf, happrox⟩ := hA m n M I hm hM Copt hopt
  obtain ⟨hcover, hcanonical⟩ := extractCover_of_raf I hm hM (A m n M I) hraf
  have hdecoded := approximation_decode I hm hM hamp Copt
    (extractCover hM (A m n M I)) hopt hcover hc (by
      rw [← hcanonical]
      exact happrox)
  simpa [inducedCover, M] using hdecoded

/-- No polynomial fixed-factor approximation, relative to an explicit
polynomial-time predicate on algorithms. -/
def NoPolynomialCoverConstApprox
    (PolynomialCover : CoverAlgorithm → Prop) : Prop :=
  ∀ c : Nat, 1 ≤ c → ∀ A, PolynomialCover A → ¬ IsCoverApprox c A

def NoPolynomialSourceRAFConstApprox
    (PolynomialRAF : SourceRAFAlgorithm → Prop) : Prop :=
  ∀ c : Nat, 1 ≤ c → ∀ A, PolynomialRAF A → ¬ IsSourceRAFApprox c A

/-- Fully formal hardness transfer.  The first premise is the standard external
SET COVER inapproximability theorem (under `P ≠ NP`); the second is the routine
closure of polynomial time under this explicit construction and extraction. -/
theorem minRAF_no_constant_factor_approx_unless_P_eq_NP
    (P_eq_NP : Prop)
    (PolynomialCover : CoverAlgorithm → Prop)
    (PolynomialRAF : SourceRAFAlgorithm → Prop)
    (setCoverHardness : ¬ P_eq_NP →
      NoPolynomialCoverConstApprox PolynomialCover)
    (reductionPolynomial : ∀ A, PolynomialRAF A →
      PolynomialCover (inducedCover A)) :
    ¬ P_eq_NP → NoPolynomialSourceRAFConstApprox PolynomialRAF := by
  intro hP c hc A hpoly happrox
  have hfactor : 1 ≤ 2 * c - 1 := by omega
  exact setCoverHardness hP (2 * c - 1) hfactor (inducedCover A)
    (reductionPolynomial A hpoly)
    (sourceRAF_approx_implies_cover_approx hc A happrox)

end SetCoverSource

end MinRAFApprox

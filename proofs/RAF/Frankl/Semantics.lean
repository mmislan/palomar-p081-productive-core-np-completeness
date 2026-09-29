module

public import proofs.RAF.Core.RAF

@[expose] public section

namespace RAF.Frankl

open RAF

variable {M R : Type*} [DecidableEq M]

/-- A reaction is retained by one RAF-pruning step when its reactants and at
least one catalyst occur at some finite stage of the molecular closure. -/
def Supported (Q : CRS M R) (C : Catalysis M R) (S : Finset R) (r : R) : Prop :=
  (∃ k, Q.inputs r ⊆ closureAt Q S k) ∧ CatalyzedFromClosure Q C S r

/-- The source-faithful one-step RAF pruning operator. -/
noncomputable def prune (Q : CRS M R) (C : Catalysis M R)
    (S : Finset R) : Finset R := by
  classical
  exact S.filter (Supported Q C S)

@[simp] theorem mem_prune (Q : CRS M R) (C : Catalysis M R)
    (S : Finset R) (r : R) :
    r ∈ prune Q C S ↔ r ∈ S ∧ Supported Q C S r := by
  classical
  simp [prune]

theorem prune_subset (Q : CRS M R) (C : Catalysis M R) (S : Finset R) :
    prune Q C S ⊆ S := by
  classical
  exact Finset.filter_subset _ _

theorem enabled_mono (Q : CRS M R) {A B : Finset M} {r : R}
    (hAB : A ⊆ B) (h : Enabled Q A r) : Enabled Q B r :=
  fun _ hx => hAB (h hx)

theorem closureStep_mono (Q : CRS M R) {S T : Finset R} {A B : Finset M}
    (hST : S ⊆ T) (hAB : A ⊆ B) :
    closureStep Q S A ⊆ closureStep Q T B := by
  classical
  intro x hx
  simp only [closureStep, Finset.mem_union, Finset.mem_biUnion] at hx ⊢
  rcases hx with hxA | ⟨r, hrS, hxout⟩
  · exact Or.inl (hAB hxA)
  · refine Or.inr ⟨r, hST hrS, ?_⟩
    by_cases hE : Enabled Q A r
    · have hEB : Enabled Q B r := enabled_mono Q hAB hE
      simpa [hE, hEB] using hxout
    · simp [hE] at hxout

theorem closureAt_mono_reactions (Q : CRS M R) {S T : Finset R}
    (hST : S ⊆ T) : ∀ k, closureAt Q S k ⊆ closureAt Q T k := by
  intro k
  induction k with
  | zero => exact fun _ hx => hx
  | succ k ih =>
      simpa [closureAt] using closureStep_mono Q hST ih

theorem supported_mono (Q : CRS M R) (C : Catalysis M R)
    {S T : Finset R} (hST : S ⊆ T) {r : R}
    (h : Supported Q C S r) : Supported Q C T r := by
  rcases h with ⟨⟨k, hk⟩, x, j, hx, hCx⟩
  refine ⟨⟨k, fun m hm => closureAt_mono_reactions Q hST k (hk hm)⟩, ?_⟩
  exact ⟨x, j, closureAt_mono_reactions Q hST j hx, hCx⟩

theorem prune_mono (Q : CRS M R) (C : Catalysis M R) {S T : Finset R}
    (hST : S ⊆ T) : prune Q C S ⊆ prune Q C T := by
  intro r hr
  rw [mem_prune] at hr ⊢
  exact ⟨hST hr.1, supported_mono Q C hST hr.2⟩

theorem isRAF_iff_nonempty_prune_eq (Q : CRS M R) (C : Catalysis M R)
    (S : Finset R) :
    IsRAF Q C S ↔ S.Nonempty ∧ prune Q C S = S := by
  constructor
  · rintro ⟨hne, hfg, hcat⟩
    refine ⟨hne, Finset.Subset.antisymm (prune_subset Q C S) ?_⟩
    intro r hr
    rw [mem_prune]
    exact ⟨hr, ⟨hfg r hr, hcat r hr⟩⟩
  · rintro ⟨hne, hfix⟩
    refine ⟨hne, ?_, ?_⟩
    · intro r hr
      have : r ∈ prune Q C S := by rw [hfix]; exact hr
      exact (mem_prune Q C S r).mp this |>.2.1
    · intro r hr
      have : r ∈ prune Q C S := by rw [hfix]; exact hr
      exact (mem_prune Q C S r).mp this |>.2.2

/-- Exact finite family of all nonempty RAFs. Classical decidability is used
only to enumerate a finite powerset; the mathematical predicate is `IsRAF`. -/
noncomputable def rafFamily (Q : CRS M R) (C : Catalysis M R) [Fintype R] :
    Finset (Finset R) := by
  classical
  exact Finset.univ.powerset.filter (IsRAF Q C)

@[simp] theorem mem_rafFamily (Q : CRS M R) (C : Catalysis M R) [Fintype R]
    (S : Finset R) : S ∈ rafFamily Q C ↔ IsRAF Q C S := by
  classical
  simp [rafFamily]

theorem isRAF_union (Q : CRS M R) (C : Catalysis M R) [DecidableEq R]
    {S T : Finset R} (hS : IsRAF Q C S) (hT : IsRAF Q C T) :
    IsRAF Q C (S ∪ T) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hS.1
    exact ⟨r, Finset.mem_union_left T hr⟩
  · intro r hr
    rcases Finset.mem_union.mp hr with hrS | hrT
    · obtain ⟨k, hk⟩ := hS.2.1 r hrS
      exact ⟨k, fun m hm => closureAt_mono_reactions Q
        (Finset.subset_union_left (s₁ := S) (s₂ := T)) k (hk hm)⟩
    · obtain ⟨k, hk⟩ := hT.2.1 r hrT
      exact ⟨k, fun m hm => closureAt_mono_reactions Q
        (Finset.subset_union_right (s₁ := S) (s₂ := T)) k (hk hm)⟩
  · intro r hr
    rcases Finset.mem_union.mp hr with hrS | hrT
    · obtain ⟨x, k, hx, hC⟩ := hS.2.2 r hrS
      exact ⟨x, k, closureAt_mono_reactions Q
        (Finset.subset_union_left (s₁ := S) (s₂ := T)) k hx, hC⟩
    · obtain ⟨x, k, hx, hC⟩ := hT.2.2 r hrT
      exact ⟨x, k, closureAt_mono_reactions Q
        (Finset.subset_union_right (s₁ := S) (s₂ := T)) k hx, hC⟩

/-- The full pruning fixed family: the empty fixed point together with all
nonempty RAFs. -/
noncomputable def fixedFamily (Q : CRS M R) (C : Catalysis M R) [Fintype R] :
    Finset (Finset R) := by
  classical
  exact insert ∅ (rafFamily Q C)

@[simp] theorem mem_fixedFamily (Q : CRS M R) (C : Catalysis M R) [Fintype R]
    (S : Finset R) : S ∈ fixedFamily Q C ↔ S = ∅ ∨ IsRAF Q C S := by
  classical
  simp [fixedFamily]

theorem fixedFamily_union_closed (Q : CRS M R) (C : Catalysis M R)
    [Fintype R] [DecidableEq R] :
    ∀ ⦃S⦄, S ∈ fixedFamily Q C →
      ∀ ⦃T⦄, T ∈ fixedFamily Q C → S ∪ T ∈ fixedFamily Q C := by
  intro S hS T hT
  rw [mem_fixedFamily] at hS hT ⊢
  rcases hS with rfl | hS
  · simpa using hT
  rcases hT with rfl | hT
  · exact Or.inr (by simpa using hS)
  · exact Or.inr (isRAF_union Q C hS hT)

/-- The union of all RAFs. If any RAF exists, this is itself a RAF and is the
unique largest RAF by inclusion. -/
noncomputable def maxRAF (Q : CRS M R) (C : Catalysis M R) [Fintype R] :
    Finset R := by
  classical
  exact (rafFamily Q C).biUnion id

theorem subset_maxRAF_of_isRAF (Q : CRS M R) (C : Catalysis M R) [Fintype R]
    {S : Finset R} (hS : IsRAF Q C S) : S ⊆ maxRAF Q C := by
  classical
  intro r hr
  simp only [maxRAF, Finset.mem_biUnion]
  exact ⟨S, (mem_rafFamily Q C S).2 hS, hr⟩

theorem isRAF_maxRAF (Q : CRS M R) (C : Catalysis M R) [Fintype R]
    (hne : (rafFamily Q C).Nonempty) : IsRAF Q C (maxRAF Q C) := by
  classical
  obtain ⟨S₀, hS₀⟩ := hne
  have hraf₀ : IsRAF Q C S₀ := (mem_rafFamily Q C S₀).1 hS₀
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hraf₀.1
    exact ⟨r, subset_maxRAF_of_isRAF Q C hraf₀ hr⟩
  · intro r hr
    simp only [maxRAF, Finset.mem_biUnion] at hr
    obtain ⟨S, hSF, hrS⟩ := hr
    have hraf : IsRAF Q C S := (mem_rafFamily Q C S).1 hSF
    obtain ⟨k, hk⟩ := hraf.2.1 r hrS
    exact ⟨k, fun m hm => closureAt_mono_reactions Q
      (subset_maxRAF_of_isRAF Q C hraf) k (hk hm)⟩
  · intro r hr
    simp only [maxRAF, Finset.mem_biUnion] at hr
    obtain ⟨S, hSF, hrS⟩ := hr
    have hraf : IsRAF Q C S := (mem_rafFamily Q C S).1 hSF
    obtain ⟨x, k, hx, hC⟩ := hraf.2.2 r hrS
    exact ⟨x, k, closureAt_mono_reactions Q
      (subset_maxRAF_of_isRAF Q C hraf) k hx, hC⟩

noncomputable def frequency (Q : CRS M R) (C : Catalysis M R) [Fintype R]
    (r : R) : Nat := by
  classical
  exact ((rafFamily Q C).filter fun S => r ∈ S).card

/-- Steel's published question: a reaction occurs in at least half of all
nonempty RAFs. -/
def SteelRAFHalf (Q : CRS M R) (C : Catalysis M R) [Fintype R] : Prop :=
  (rafFamily Q C).Nonempty →
    ∃ r : R, (rafFamily Q C).card ≤ 2 * frequency Q C r

/-- Standard Frankl for the fixed family after adjoining the empty fixed
point. Since the empty set has no occurrences, this is one count stronger. -/
def RAFFixedFrankl (Q : CRS M R) (C : Catalysis M R) [Fintype R] : Prop :=
  (rafFamily Q C).Nonempty →
    ∃ r : R, (rafFamily Q C).card + 1 ≤ 2 * frequency Q C r

theorem rafFixedFrankl_implies_steelRAFHalf
    (Q : CRS M R) (C : Catalysis M R) [Fintype R] :
    RAFFixedFrankl Q C → SteelRAFHalf Q C := by
  intro hStrong hne
  obtain ⟨r, hr⟩ := hStrong hne
  exact ⟨r, le_trans (Nat.le_succ _) hr⟩

end RAF.Frankl

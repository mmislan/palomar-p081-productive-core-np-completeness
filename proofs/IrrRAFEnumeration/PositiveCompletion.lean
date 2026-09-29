module

public import proofs.IrrRAFEnumeration.RAFCompletion

@[expose] public section

namespace IrrRAFEnumeration.PositiveCompletion

variable {α : Type*} [DecidableEq α]

/-- Positive viability witnesses with downward-hereditary exclusions. -/
def Available (P : Finset α → Prop) (G : Finset (Finset α)) (U : Finset α) : Prop :=
  ∃ S, S ⊆ U ∧ P S ∧ ∀ I ∈ G, ¬ I ⊆ S

omit [DecidableEq α] in
theorem available_mono {P : Finset α → Prop} {G : Finset (Finset α)}
    {U V : Finset α} (hUV : U ⊆ V) : Available P G U → Available P G V := by
  rintro ⟨S, hS, hP, hG⟩
  exact ⟨S, hS.trans hUV, hP, hG⟩

/-- One actual finite deletion sweep, parametrized by its Boolean oracle. -/
def sweep (oracle : Finset α → Bool) : List α → Finset α → Finset α
  | [], U => U
  | r :: rs, U => sweep oracle rs (if oracle (U.erase r) then U.erase r else U)

theorem sweep_subset (oracle : Finset α → Bool) (rs : List α) (U : Finset α) :
    sweep oracle rs U ⊆ U := by
  induction rs generalizing U with
  | nil => exact Finset.Subset.rfl
  | cons r rs ih =>
    simp only [sweep]
    split
    · exact (ih _).trans (Finset.erase_subset _ _)
    · exact ih _

/-- A failed deletion stays failed after every later successful deletion.
Only the container oracle is monotone; viability itself need not be. -/
theorem sweep_correct (A : Finset α → Prop) (hmono : Monotone A)
    (oracle : Finset α → Bool) (horacle : ∀ U, oracle U = true ↔ A U)
    (rs : List α) (U : Finset α) (hU : A U) :
    A (sweep oracle rs U) ∧
      ∀ r ∈ rs, r ∈ sweep oracle rs U → ¬ A ((sweep oracle rs U).erase r) := by
  induction rs generalizing U with
  | nil => exact ⟨hU, by simp⟩
  | cons r rs ih =>
    by_cases hr : oracle (U.erase r) = true
    · simp only [sweep, hr, ↓reduceIte]
      obtain ⟨ha, hd⟩ := ih (U.erase r) ((horacle _).mp hr)
      refine ⟨ha, ?_⟩
      intro x hx hxu
      rcases List.mem_cons.mp hx with hxr | hxrs
      · subst x
        have := sweep_subset oracle rs (U.erase r) hxu
        exact False.elim ((Finset.mem_erase.mp this).1 rfl)
      · exact hd x hxrs hxu
    · simp only [sweep, hr]
      obtain ⟨ha, hd⟩ := ih U hU
      refine ⟨ha, ?_⟩
      intro x hx hxu
      rcases List.mem_cons.mp hx with hxr | hxrs
      · subst x
        intro hdel
        apply hr
        apply (horacle _).mpr
        exact hmono (Finset.erase_subset_erase r (sweep_subset oracle rs U)) hdel
      · exact hd x hxrs hxu

theorem sweep_minimal (A : Finset α → Prop) (hmono : Monotone A)
    (oracle : Finset α → Bool) (horacle : ∀ U, oracle U = true ↔ A U)
    (rs : List α) (U : Finset α) (hcover : ∀ r ∈ U, r ∈ rs) (hU : A U) :
    Minimal A (sweep oracle rs U) := by
  obtain ⟨ha, hd⟩ := sweep_correct A hmono oracle horacle rs U hU
  refine ⟨ha, ?_⟩
  intro V hV hVU r hr
  by_contra hrV
  have hsmall : V ⊆ (sweep oracle rs U).erase r := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨by intro he; subst x; exact hrV hx, hVU hx⟩
  exact hd r (hcover r (sweep_subset oracle rs U hr)) hr (hmono hsmall hV)

omit [DecidableEq α] in
/-- Minimal positive-witness containers are themselves new minimal viable sets. -/
theorem minimal_available {P : Finset α → Prop} {G : Finset (Finset α)}
    {U : Finset α} (hU : Minimal (Available P G) U) :
    Minimal P U ∧ ∀ I ∈ G, ¬ I ⊆ U := by
  obtain ⟨S, hSU, hP, hG⟩ := hU.1
  have hUS : U ⊆ S := hU.2 ⟨S, Finset.Subset.rfl, hP, hG⟩ hSU
  have heq : S = U := Finset.Subset.antisymm hSU hUS
  subst S
  refine ⟨⟨hP, ?_⟩, hG⟩
  intro V hV hVU
  apply hU.2 ?_ hVU
  exact ⟨V, Finset.Subset.rfl, hV, fun I hI hIV => hG I hI (hIV.trans hVU)⟩

theorem sweep_new_minimal {P : Finset α → Prop} {G : Finset (Finset α)}
    (oracle : Finset α → Bool) (horacle : ∀ U, oracle U = true ↔ Available P G U)
    (rs : List α) (U : Finset α) (hcover : ∀ r ∈ U, r ∈ rs)
    (hU : Available P G U) :
    Minimal P (sweep oracle rs U) ∧ sweep oracle rs U ∉ G := by
  obtain ⟨hmin, havoid⟩ := minimal_available
    (sweep_minimal (Available P G) (fun _ _ h => available_mono h)
      oracle horacle rs U hcover hU)
  exact ⟨hmin, fun hmem => havoid _ hmem Finset.Subset.rfl⟩

variable [Fintype α]

omit [DecidableEq α] in
/-- The positive completion query stops exactly when every minimal set is known. -/
theorem available_univ_iff_missing {P : Finset α → Prop} {G : Finset (Finset α)}
    (hG : ∀ I ∈ G, Minimal P I) :
    Available P G Finset.univ ↔ ∃ I, Minimal P I ∧ I ∉ G := by
  constructor
  · rintro ⟨S, _, hS, havoid⟩
    obtain ⟨I, hIS, hI⟩ := exists_minimal_subset P hS
    exact ⟨I, hI, fun hi => havoid I hi hIS⟩
  · rintro ⟨I, hI, hnew⟩
    refine ⟨I, Finset.subset_univ I, hI.1, ?_⟩
    intro J hJ hJI
    have hIJ := hI.2 (hG J hJ).1 hJI
    have heq : I = J := Finset.Subset.antisymm hIJ hJI
    exact hnew (heq.symm ▸ hJ)

/-- Docking to ordinary RAFs, without irreducibility in the witness predicate. -/
theorem raf_sweep_new {M R : Type*} [Fintype R] [DecidableEq M] [DecidableEq R]
    (Q : RAF.CRS M R) (C : RAF.Catalysis M R) (G : Finset (Finset R))
    (oracle : Finset R → Bool)
    (horacle : ∀ U, oracle U = true ↔ Available (RAF.IsRAF Q C) G U)
    (rs : List R) (hcover : ∀ r, r ∈ rs)
    (h : Available (RAF.IsRAF Q C) G Finset.univ) :
    sweep oracle rs Finset.univ ∈ irrRAFFamily Q C ∧
      sweep oracle rs Finset.univ ∉ G := by
  obtain ⟨hm, hn⟩ := sweep_new_minimal oracle horacle rs Finset.univ
    (fun r _ => hcover r) h
  exact ⟨(mem_irrRAFFamily Q C _).mpr hm, hn⟩

end IrrRAFEnumeration.PositiveCompletion

module

public import proofs.RAF.Frankl.Semantics

@[expose] public section

namespace RAF.Frankl

open RAF

variable {M R : Type*} [DecidableEq M]

/-- Catalysis after food generation depends only on food catalysts and on
products of selected reactions.  This is the fixed directed-graph part of RAF
semantics. -/
def ProductGraphCatalyzed (Q : CRS M R) (C : Catalysis M R)
    (S : Finset R) : Prop :=
  ∀ r ∈ S,
    (∃ x ∈ Q.food, C x r) ∨
    ∃ u ∈ S, ∃ x ∈ Q.outputs u, C x r

theorem mem_closureAt_imp_food_or_output
    (Q : CRS M R) (S : Finset R) {x : M} :
    ∀ {k}, x ∈ closureAt Q S k →
      x ∈ Q.food ∨ ∃ r ∈ S, x ∈ Q.outputs r := by
  intro k hx
  induction k with
  | zero =>
      exact Or.inl hx
  | succ k ih =>
      simp only [closureAt, closureStep, Finset.mem_union,
        Finset.mem_biUnion] at hx
      rcases hx with hx | ⟨r, hr, hx⟩
      · exact ih hx
      · by_cases hEnabled : Enabled Q (closureAt Q S k) r
        · exact Or.inr ⟨r, hr, by simpa [hEnabled] using hx⟩
        · simp [hEnabled] at hx

theorem output_mem_some_closureAt_of_foodGenerated
    (Q : CRS M R) {S : Finset R} (hfg : FoodGenerated Q S)
    {r : R} (hr : r ∈ S) {x : M} (hx : x ∈ Q.outputs r) :
    ∃ k, x ∈ closureAt Q S k := by
  obtain ⟨k, hk⟩ := hfg r hr
  refine ⟨k + 1, ?_⟩
  simp only [closureAt, closureStep, Finset.mem_union,
    Finset.mem_biUnion]
  have henabled : Enabled Q (closureAt Q S k) r := hk
  exact Or.inr ⟨r, hr, by simpa [henabled] using hx⟩

theorem catalyzedFromClosure_iff_productGraph
    (Q : CRS M R) (C : Catalysis M R) {S : Finset R}
    (hfg : FoodGenerated Q S) (r : R) :
    CatalyzedFromClosure Q C S r ↔
      (∃ x ∈ Q.food, C x r) ∨
      ∃ u ∈ S, ∃ x ∈ Q.outputs u, C x r := by
  constructor
  · rintro ⟨x, k, hx, hcat⟩
    rcases mem_closureAt_imp_food_or_output Q S hx with hxfood | ⟨u, hu, hxout⟩
    · exact Or.inl ⟨x, hxfood, hcat⟩
    · exact Or.inr ⟨u, hu, x, hxout, hcat⟩
  · rintro (⟨x, hxfood, hcat⟩ | ⟨u, hu, x, hxout, hcat⟩)
    · exact ⟨x, 0, hxfood, hcat⟩
    · obtain ⟨k, hx⟩ :=
        output_mem_some_closureAt_of_foodGenerated Q hfg hu hxout
      exact ⟨x, k, hx, hcat⟩

theorem foodGenerated_union (Q : CRS M R) [DecidableEq R]
    {S T : Finset R} (hS : FoodGenerated Q S) (hT : FoodGenerated Q T) :
    FoodGenerated Q (S ∪ T) := by
  intro r hr
  rcases Finset.mem_union.mp hr with hrS | hrT
  · obtain ⟨k, hk⟩ := hS r hrS
    exact ⟨k, fun x hx => closureAt_mono_reactions Q
      (Finset.subset_union_left (s₁ := S) (s₂ := T)) k (hk hx)⟩
  · obtain ⟨k, hk⟩ := hT r hrT
    exact ⟨k, fun x hx => closureAt_mono_reactions Q
      (Finset.subset_union_right (s₁ := S) (s₂ := T)) k (hk hx)⟩

@[simp] theorem foodGenerated_empty (Q : CRS M R) :
    FoodGenerated Q (∅ : Finset R) := by
  intro r hr
  simp at hr

theorem closureAt_erase_eq_of_not_enabled_before
    (Q : CRS M R) [DecidableEq R] (S : Finset R) (r : R) (K : Nat)
    (hnot : ∀ j < K, ¬ Enabled Q (closureAt Q S j) r) :
    ∀ j ≤ K, closureAt Q (S.erase r) j = closureAt Q S j := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
      have hjlt : j < K := Nat.lt_of_succ_le hj
      have ihj : closureAt Q (S.erase r) j = closureAt Q S j :=
        ih (Nat.le_trans (Nat.le_succ j) hj)
      classical
      simp only [closureAt, closureStep, ihj]
      apply congrArg (fun T : Finset M => closureAt Q S j ∪ T)
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_erase]
      constructor
      · rintro ⟨u, ⟨hur, huS⟩, hxu⟩
        exact ⟨u, huS, hxu⟩
      · rintro ⟨u, huS, hxu⟩
        by_cases hur : u = r
        · subst u
          simp [hnot j hjlt] at hxu
        · exact ⟨u, ⟨hur, huS⟩, hxu⟩

/-- Food-generation feasibility is accessible: delete a reaction whose
inputs become available last. Together with `foodGenerated_union`, this is
the antimatroid structure hidden in general RAF semantics. -/
theorem foodGenerated_accessible (Q : CRS M R) [DecidableEq R]
    {S : Finset R} (hne : S.Nonempty) (hfg : FoodGenerated Q S) :
    ∃ r ∈ S, FoodGenerated Q (S.erase r) := by
  let rank : R → Nat := fun r => if hr : r ∈ S then Nat.find (hfg r hr) else 0
  obtain ⟨r, hrS, hrmax⟩ := Finset.exists_max_image S rank hne
  refine ⟨r, hrS, ?_⟩
  intro u huErase
  have huS : u ∈ S := (Finset.mem_erase.mp huErase).2
  have hur : u ≠ r := (Finset.mem_erase.mp huErase).1
  have hru : rank u ≤ rank r := hrmax u huS
  have hrankr : rank r = Nat.find (hfg r hrS) := by simp [rank, hrS]
  have hranku : rank u = Nat.find (hfg u huS) := by simp [rank, huS]
  have hnot : ∀ j < rank r, ¬ Enabled Q (closureAt Q S j) r := by
    intro j hj henabled
    rw [hrankr] at hj
    exact (Nat.find_min (hfg r hrS) hj) henabled
  refine ⟨rank u, ?_⟩
  have hclosure := closureAt_erase_eq_of_not_enabled_before Q S r (rank r) hnot
    (rank u) hru
  rw [hclosure]
  rw [hranku]
  exact Nat.find_spec (hfg u huS)

theorem foodGenerated_insert_seed (Q : CRS M R) [DecidableEq R]
    {S : Finset R} {q : R} (hS : FoodGenerated Q S)
    (hq : SeedReaction Q q) : FoodGenerated Q (insert q S) := by
  intro r hr
  rcases Finset.mem_insert.mp hr with rfl | hrS
  · exact ⟨0, hq⟩
  · obtain ⟨k, hk⟩ := hS r hrS
    exact ⟨k, fun x hx => closureAt_mono_reactions Q
      (Finset.subset_insert q S) k (hk hx)⟩

/-- Exact factorization of general RAF semantics into the food-generation
feasible family and a fixed product-catalysis digraph condition. -/
theorem isRAF_iff_foodGenerated_and_productGraph
    (Q : CRS M R) (C : Catalysis M R) (S : Finset R) :
    IsRAF Q C S ↔
      S.Nonempty ∧ FoodGenerated Q S ∧ ProductGraphCatalyzed Q C S := by
  constructor
  · rintro ⟨hne, hfg, hcat⟩
    refine ⟨hne, hfg, ?_⟩
    intro r hr
    exact (catalyzedFromClosure_iff_productGraph Q C hfg r).mp (hcat r hr)
  · rintro ⟨hne, hfg, hgraph⟩
    refine ⟨hne, hfg, ?_⟩
    intro r hr
    exact (catalyzedFromClosure_iff_productGraph Q C hfg r).mpr (hgraph r hr)

/-- At a food-enabled reaction, addition to an existing RAF has no hidden
food-generation obstruction.  It succeeds exactly when the new reaction has
a food catalyst or a product catalyst in the enlarged set. -/
theorem isRAF_insert_seed_iff (Q : CRS M R) (C : Catalysis M R)
    [DecidableEq R] {S : Finset R} {q : R} (hS : IsRAF Q C S)
    (hq : SeedReaction Q q) :
    IsRAF Q C (insert q S) ↔
      (∃ x ∈ Q.food, C x q) ∨
      ∃ u ∈ insert q S, ∃ x ∈ Q.outputs u, C x q := by
  have hfg : FoodGenerated Q (insert q S) :=
    foodGenerated_insert_seed Q hS.2.1 hq
  rw [isRAF_iff_foodGenerated_and_productGraph Q C (insert q S)]
  constructor
  · rintro ⟨_, _, hgraph⟩
    exact hgraph q (Finset.mem_insert_self q S)
  · intro hqcat
    refine ⟨Finset.insert_nonempty q S, hfg, ?_⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hrS
    · exact hqcat
    · rcases (catalyzedFromClosure_iff_productGraph Q C hS.2.1 r).mp
          (hS.2.2 r hrS) with hfood | ⟨u, huS, hu⟩
      · exact Or.inl hfood
      · exact Or.inr ⟨u, Finset.mem_insert_of_mem huS, hu⟩

end RAF.Frankl

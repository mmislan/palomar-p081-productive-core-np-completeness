module

public import proofs.MinRAFApprox.Gadgets.SetCoverSource

@[expose] public section

namespace MinRAFApprox.SetCoverSource

open RAF MinRAFApprox.Reaction

variable {m n M : Nat}

theorem block_support_forces_last
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n)) (hM : 0 < M)
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)))
    (hgraph : RAF.Frankl.ProductGraphCatalyzed (crs m n M) (catalysis I) S)
    {j : Fin n} {k : Fin M} (hkS : block (U := Fin m) j k ∈ S) :
    block (U := Fin m) j (lastFin M hM) ∈ S := by
  rcases hgraph _ hkS with hfood | ⟨r, hrS, x, hxout, hcat⟩
  · rcases hfood with ⟨x, hx, hcat⟩
    change x ∈ ({MinRAFApprox.Molecule.food} : Finset (MinRAFApprox.Molecule n M)) at hx
    simp at hx
    subst x
    simp [catalysis] at hcat
  · cases r with
    | gate i =>
        change x ∈ ({MinRAFApprox.Molecule.y i.val} : Finset (MinRAFApprox.Molecule n M)) at hxout
        simp at hxout
        subst x
        simp [catalysis] at hcat
    | block j' l =>
        change x ∈ ({MinRAFApprox.Molecule.z j' l} : Finset (MinRAFApprox.Molecule n M)) at hxout
        simp at hxout
        subst x
        rcases hcat with ⟨hlast, rfl⟩
        have hl : l = lastFin M hM := Fin.ext (by simp [lastFin, hlast])
        simpa [hl] using hrS

theorem gate_support_yields_cover_block
    (I : MinRAFApprox.SetCoverInstance (Fin m) (Fin n)) (hM : 0 < M)
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)))
    (hgraph : RAF.Frankl.ProductGraphCatalyzed (crs m n M) (catalysis I) S)
    {i : Fin m} (hiS : gate (J := Fin n) (K := Fin M) i ∈ S) :
    ∃ j : Fin n, block (U := Fin m) j (lastFin M hM) ∈ S ∧ i ∈ I.sets j := by
  rcases hgraph _ hiS with hfood | ⟨r, hrS, x, hxout, hcat⟩
  · rcases hfood with ⟨x, hx, hcat⟩
    change x ∈ ({MinRAFApprox.Molecule.food} : Finset (MinRAFApprox.Molecule n M)) at hx
    simp at hx
    subst x
    simp [catalysis] at hcat
  · cases r with
    | gate q =>
        change x ∈ ({MinRAFApprox.Molecule.y q.val} : Finset (MinRAFApprox.Molecule n M)) at hxout
        simp at hxout
        subst x
        simp [catalysis] at hcat
    | block j l =>
        change x ∈ ({MinRAFApprox.Molecule.z j l} : Finset (MinRAFApprox.Molecule n M)) at hxout
        simp at hxout
        subst x
        rcases hcat with ⟨hlast, hiCover⟩
        have hl : l = lastFin M hM := Fin.ext (by simp [lastFin, hlast])
        exact ⟨j, by simpa [hl] using hrS, hiCover⟩

theorem gate_predecessor_of_foodGenerated
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)))
    (hfg : FoodGenerated (crs m n M) S) {i : Fin m}
    (hiS : gate (J := Fin n) (K := Fin M) i ∈ S) (hi : i.val ≠ 0) :
    gate (J := Fin n) (K := Fin M) (predFin i) ∈ S := by
  obtain ⟨stage, hinputs⟩ := hfg _ hiS
  have hyInput : MinRAFApprox.Molecule.y (i.val - 1) ∈
      (crs m n M).inputs (gate (J := Fin n) (K := Fin M) i) := by
    simp [crs, hi]
  obtain ⟨q, hqS, hqval⟩ := y_origin S (hinputs hyInput)
  have hq : q = predFin i := Fin.ext (by simpa [predFin] using hqval)
  simpa [hq] using hqS

theorem block_predecessor_of_foodGenerated
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)))
    (hfg : FoodGenerated (crs m n M) S) {j : Fin n} {k : Fin M}
    (hkS : block (U := Fin m) j k ∈ S) (hk : k.val ≠ 0) :
    block (U := Fin m) j (predFin k) ∈ S := by
  obtain ⟨stage, hinputs⟩ := hfg _ hkS
  have hzInput : MinRAFApprox.Molecule.z j (predFin k) ∈
      (crs m n M).inputs (block (U := Fin m) j k) := by
    simp [crs, hk]
  exact z_origin S (hinputs hzInput)

theorem zero_block_forces_last_gate
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)))
    (hfg : FoodGenerated (crs m n M) S) (hm : 0 < m)
    {j : Fin n} {k : Fin M} (hkS : block (U := Fin m) j k ∈ S)
    (hk : k.val = 0) :
    gate (J := Fin n) (K := Fin M) (lastFin m hm) ∈ S := by
  obtain ⟨stage, hinputs⟩ := hfg _ hkS
  have hyInput : MinRAFApprox.Molecule.y (m - 1) ∈
      (crs m n M).inputs (block (U := Fin m) j k) := by
    simp [crs, hk]
  obtain ⟨q, hqS, hqval⟩ := y_origin S (hinputs hyInput)
  have hq : q = lastFin m hm := Fin.ext (by simp [lastFin, hqval])
  simpa [hq] using hqS

theorem block_prefix
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)))
    (hfg : FoodGenerated (crs m n M) S) (j : Fin n) (k : Fin M)
    (hkS : block (U := Fin m) j k ∈ S) :
    ∀ l : Fin M, l.val ≤ k.val → block (U := Fin m) j l ∈ S := by
  induction hval : k.val using Nat.strong_induction_on generalizing k with
  | h t ih =>
      intro l hle
      by_cases hlt : l.val < t
      · have ht : t ≠ 0 := by omega
        have hk0 : k.val ≠ 0 := by omega
        have hpred := block_predecessor_of_foodGenerated S hfg hkS hk0
        exact ih (t - 1) (by omega) (predFin k) hpred
          (by simp [predFin] at *; omega) l (by simp [predFin] at *; omega)
      · have hlk : l = k := Fin.ext (by omega)
        simpa [hlk] using hkS

theorem gate_prefix
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)))
    (hfg : FoodGenerated (crs m n M) S) (i : Fin m)
    (hiS : gate (J := Fin n) (K := Fin M) i ∈ S) :
    ∀ q : Fin m, q.val ≤ i.val → gate (J := Fin n) (K := Fin M) q ∈ S := by
  induction hval : i.val using Nat.strong_induction_on generalizing i with
  | h t ih =>
      intro q hle
      by_cases hlt : q.val < t
      · have hi0 : i.val ≠ 0 := by omega
        have hpred := gate_predecessor_of_foodGenerated S hfg hiS hi0
        exact ih (t - 1) (by omega) (predFin i) hpred
          (by simp [predFin] at *; omega) q (by simp [predFin] at *; omega)
      · have hqi : q = i := Fin.ext (by omega)
        simpa [hqi] using hiS

end MinRAFApprox.SetCoverSource

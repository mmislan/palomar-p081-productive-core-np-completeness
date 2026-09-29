module

public import proofs.MinRAFApprox.Gadgets.SetCoverProvenance

@[expose] public section

namespace MinRAFApprox.SetCoverSource

open RAF RAF.Frankl MinRAFApprox.Reaction

variable {m n M : Nat}

theorem closureAt_subset_succ
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M))) (stage : Nat) :
    closureAt (crs m n M) S stage ⊆ closureAt (crs m n M) S (stage + 1) := by
  intro x hx
  simp only [closureAt, closureStep, Finset.mem_union]
  exact Or.inl hx

theorem closureAt_mono_time
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M)))
    {a b : Nat} (hab : a ≤ b) :
    closureAt (crs m n M) S a ⊆ closureAt (crs m n M) S b := by
  induction b, hab using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ b _ ih => exact Finset.Subset.trans ih (closureAt_subset_succ S b)

theorem food_reachable
    (S : Finset (MinRAFApprox.Reaction (Fin m) (Fin n) (Fin M))) (stage : Nat) :
    MinRAFApprox.Molecule.food ∈ closureAt (crs m n M) S stage := by
  exact closureAt_mono_time S (Nat.zero_le stage) (by simp [closureAt, crs])

theorem canonical_y_reachable (C : Finset (Fin n)) (i : Fin m) :
    MinRAFApprox.Molecule.y i.val ∈
      closureAt (crs m n M) (MinRAFApprox.canonicalRAF C) (i.val + 1) := by
  induction hval : i.val using Nat.strong_induction_on generalizing i with
  | h t ih =>
      simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion]
      apply Or.inr
      refine ⟨gate i, MinRAFApprox.gate_mem_canonicalRAF C i, ?_⟩
      have henabled : Enabled (crs m n M)
          (closureAt (crs m n M) (MinRAFApprox.canonicalRAF C) t) (gate i) := by
        intro x hx
        by_cases hi : i.val = 0
        · have hxfood : x = MinRAFApprox.Molecule.food := by
            simpa [crs, hi] using hx
          subst x
          exact food_reachable _ t
        · have hxparts : x = MinRAFApprox.Molecule.food ∨
              x = MinRAFApprox.Molecule.y (i.val - 1) := by
            simpa [crs, hi] using hx
          rcases hxparts with rfl | rfl
          · exact food_reachable _ t
          · have hprev := ih (t - 1) (by omega) (predFin i)
                (by simp [predFin] at *; omega)
            have hidx : i.val - 1 = t - 1 := by omega
            have hstage : t - 1 + 1 = t := by omega
            rw [hidx]
            simpa only [hstage] using hprev
      change MinRAFApprox.Molecule.y t ∈
        (if Enabled (crs m n M)
          (closureAt (crs m n M) (MinRAFApprox.canonicalRAF C) t) (gate i)
        then (crs m n M).outputs (gate i) else ∅)
      rw [ite_eq_left henabled]
      change MinRAFApprox.Molecule.y t ∈
        ({MinRAFApprox.Molecule.y i.val} : Finset (MinRAFApprox.Molecule n M))
      simp [hval]

theorem canonical_z_reachable (hm : 0 < m) (C : Finset (Fin n))
    {j : Fin n} (hjC : j ∈ C) (k : Fin M) :
    MinRAFApprox.Molecule.z j k ∈
      closureAt (crs m n M) (MinRAFApprox.canonicalRAF C) (m + k.val + 1) := by
  induction hval : k.val using Nat.strong_induction_on generalizing k with
  | h t ih =>
      simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion]
      apply Or.inr
      refine ⟨block j k, (MinRAFApprox.block_mem_canonicalRAF C j k).2 hjC, ?_⟩
      have henabled : Enabled (crs m n M)
          (closureAt (crs m n M) (MinRAFApprox.canonicalRAF C) (m + t))
          (block j k) := by
        intro x hx
        by_cases hk : k.val = 0
        · have hxparts : x = MinRAFApprox.Molecule.food ∨
              x = MinRAFApprox.Molecule.y (m - 1) := by
            simpa [crs, hk] using hx
          rcases hxparts with rfl | rfl
          · exact food_reachable _ (m + t)
          · have hy := canonical_y_reachable (M := M) C (lastFin m hm)
            have hym : (lastFin m hm).val + 1 = m := by simp [lastFin]; omega
            exact closureAt_mono_time _ (by simp [hym]) hy
        · have hxparts : x = MinRAFApprox.Molecule.food ∨
              x = MinRAFApprox.Molecule.z j (predFin k) := by
            simpa [crs, hk] using hx
          rcases hxparts with rfl | rfl
          · exact food_reachable _ (m + t)
          · have hprev := ih (t - 1) (by omega) (predFin k)
                (by simp [predFin] at *; omega)
            have hstage : m + (t - 1) + 1 = m + t := by omega
            simpa only [hstage] using hprev
      change MinRAFApprox.Molecule.z j k ∈
        (if Enabled (crs m n M)
          (closureAt (crs m n M) (MinRAFApprox.canonicalRAF C) (m + t)) (block j k)
        then (crs m n M).outputs (block j k) else ∅)
      rw [ite_eq_left henabled]
      change MinRAFApprox.Molecule.z j k ∈
        ({MinRAFApprox.Molecule.z j k} : Finset (MinRAFApprox.Molecule n M))
      simp

theorem canonical_foodGenerated (hm : 0 < m) (C : Finset (Fin n)) :
    FoodGenerated (crs m n M) (MinRAFApprox.canonicalRAF C) := by
  intro r hr
  cases r with
  | gate i =>
      refine ⟨i.val, ?_⟩
      intro x hx
      by_cases hi : i.val = 0
      · have hxfood : x = MinRAFApprox.Molecule.food := by simpa [crs, hi] using hx
        subst x
        exact food_reachable _ i.val
      · have hxparts : x = MinRAFApprox.Molecule.food ∨
            x = MinRAFApprox.Molecule.y (i.val - 1) := by
          simpa [crs, hi] using hx
        rcases hxparts with rfl | rfl
        · exact food_reachable _ i.val
        · have hy := canonical_y_reachable (M := M) C (predFin i)
          have hpredval : (predFin i).val = i.val - 1 := by rfl
          rw [hpredval] at hy
          have hstage' : i.val - 1 + 1 = i.val := by omega
          rw [hstage'] at hy
          exact hy
  | block j k =>
      have hjC := (MinRAFApprox.block_mem_canonicalRAF C j k).1 hr
      refine ⟨m + k.val, ?_⟩
      intro x hx
      by_cases hk : k.val = 0
      · have hxparts : x = MinRAFApprox.Molecule.food ∨
            x = MinRAFApprox.Molecule.y (m - 1) := by
          simpa [crs, hk] using hx
        rcases hxparts with rfl | rfl
        · exact food_reachable _ (m + k.val)
        · have hy := canonical_y_reachable (M := M) C (lastFin m hm)
          have hlastval : (lastFin m hm).val = m - 1 := by rfl
          rw [hlastval] at hy
          have hstage' : m - 1 + 1 = m + k.val := by omega
          rw [hstage'] at hy
          exact hy
      · have hxparts : x = MinRAFApprox.Molecule.food ∨
            x = MinRAFApprox.Molecule.z j (predFin k) := by
          simpa [crs, hk] using hx
        rcases hxparts with rfl | rfl
        · exact food_reachable _ (m + k.val)
        · have hz := canonical_z_reachable hm C hjC (predFin k)
          have hstage : m + (predFin k).val + 1 = m + k.val := by
            simp [predFin]
            omega
          simpa [hstage] using hz

end MinRAFApprox.SetCoverSource

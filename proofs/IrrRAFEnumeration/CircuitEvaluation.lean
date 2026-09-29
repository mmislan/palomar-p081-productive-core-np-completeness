module

public import proofs.IrrRAFEnumeration.CircuitBijection

@[expose] public section

namespace IrrRAFEnumeration.CircuitSource

open RAF RAF.Frankl

/-- Finite positive rule derivations, independently of molecular closure. -/
inductive Derives {n w q : Nat} (D : Rules n w q) (T : Finset (Fin n)) : Fin w → Prop
  | input (i : Fin n) (hi : i ∈ T) : Derives D T (D.inputWire i)
  | rule (j : Fin q) (hneeds : ∀ v ∈ D.needs j, Derives D T v)
      (v : Fin w) (hv : v ∈ D.produces j) : Derives D T v

theorem closureAt_mono_time {M R : Type*} [DecidableEq M]
    (Q : CRS M R) (S : Finset R) : Monotone (closureAt Q S) := by
  apply monotone_nat_of_le_succ
  intro k
  exact Finset.subset_union_left

theorem finite_signals_reached {n w q : Nat} (D : Rules n w q)
    (S : Finset (Reaction n q)) (V : Finset (Fin w))
    (h : ∀ v ∈ V, ∃ k, Molecule.wire v ∈ closureAt (crs D) S k) :
    ∃ k, ∀ v ∈ V, Molecule.wire v ∈ closureAt (crs D) S k := by
  induction V using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert v V _ ih =>
      obtain ⟨a, ha⟩ := h v (by simp)
      obtain ⟨b, hb⟩ := ih (fun u hu => h u (by simp [hu]))
      refine ⟨max a b, ?_⟩
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact closureAt_mono_time (crs D) S (Nat.le_max_left _ _) ha
      · exact closureAt_mono_time (crs D) S (Nat.le_max_right _ _) (hb u hu)

theorem derives_imp_reached {n w q : Nat} (D : Rules n w q)
    (T : Finset (Fin n)) {v : Fin w} (h : Derives D T v) :
    ∃ k, Molecule.wire v ∈ closureAt (crs D) ((canonical T).erase reset) k := by
  induction h with
  | input i hi =>
      refine ⟨1, ?_⟩
      have hr : (Sum.inl i : Reaction n q) ∈ (canonical T).erase reset := by
        simp [reset, hi]
      simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion]
      exact Or.inr ⟨Sum.inl i, hr, by simp [crs, Enabled]⟩
  | rule j _ v hv ih =>
      obtain ⟨k, hk⟩ := finite_signals_reached D ((canonical T).erase reset) (D.needs j) ih
      let b : Fin (q + 1) := ⟨j.val, by omega⟩
      have hb : b.val < q := j.isLt
      have hr : (Sum.inr b : Reaction n q) ∈ (canonical T).erase reset := by
        have hne : (Sum.inr b : Reaction n q) ≠ reset := by
          intro heq
          have he : b = Fin.last q := Sum.inr.inj heq
          have := congrArg Fin.val he
          simp only [Fin.val_last] at this
          omega
        simp [hne]
      have he : Enabled (crs D) (closureAt (crs D) ((canonical T).erase reset) k)
          (Sum.inr b) := by
        intro x hx
        simp only [crs, hb, dite_true, Finset.mem_image] at hx
        obtain ⟨u, hu, rfl⟩ := hx
        exact hk u hu
      refine ⟨k + 1, ?_⟩
      simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion]
      exact Or.inr ⟨Sum.inr b, hr, by
        rw [ite_eq_left he]
        simp [crs, hb, b, hv]⟩

theorem reached_imp_derives {n w q : Nat} (D : Rules n w q)
    (T : Finset (Fin n)) : ∀ k, ∀ v : Fin w,
    Molecule.wire v ∈ closureAt (crs D) ((canonical T).erase reset) k →
      Derives D T v := by
  intro k
  induction k with
  | zero => intro v hv; simp [closureAt, crs] at hv
  | succ k ih =>
      intro v hv
      simp only [closureAt, closureStep, Finset.mem_union, Finset.mem_biUnion] at hv
      rcases hv with hv | ⟨r, hr, hv⟩
      · exact ih v hv
      · by_cases he : Enabled (crs D)
            (closureAt (crs D) ((canonical T).erase reset) k) r
        · rw [ite_eq_left he] at hv
          have hrc := Finset.mem_erase.mp hr
          cases r with
          | inl i =>
              have hi : i ∈ T := (inl_mem_canonical T i).mp hrc.2
              have hv' : v = D.inputWire i := by simpa [crs] using hv
              rw [hv']
              exact Derives.input i hi
          | inr b =>
              have hb : b.val < q := by
                by_contra hlt
                have hblast : b = Fin.last q := by
                  apply Fin.ext
                  simp only [Fin.val_last]
                  omega
                exact hrc.1 (by simp [reset, hblast])
              let j : Fin q := ⟨b.val, hb⟩
              have hp : v ∈ D.produces j := by simpa [crs, hb, j] using hv
              apply Derives.rule j _ v hp
              intro u hu
              apply ih u
              apply he
              simp [crs, hb, j] at hu ⊢
              exact hu
        · simp [he] at hv

theorem accepts_iff_derives {n w q : Nat} (D : Rules n w q)
    (T : Finset (Fin n)) : Accepts D T ↔ Derives D T D.output := by
  constructor
  · rintro ⟨k, hk⟩
    exact reached_imp_derives D T k D.output hk
  · exact derives_imp_reached D T

end IrrRAFEnumeration.CircuitSource

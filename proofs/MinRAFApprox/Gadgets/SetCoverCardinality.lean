module

public import proofs.MinRAFApprox.Gadgets.SetCoverBijection

@[expose] public section

namespace MinRAFApprox.SetCoverSource

variable {m n M : Nat}

/-- Forget the membership proof and expose a canonical reaction as either a
gate index or a selected-set/block-coordinate pair. -/
noncomputable def canonicalRAFMap (C : Finset (Fin n)) :
    {r // r ∈ MinRAFApprox.canonicalRAF (U := Fin m) (K := Fin M) C} →
      (Fin m) ⊕ ({j // j ∈ C} × Fin M) := fun r => by
    rcases r with ⟨r, hr⟩
    cases r with
    | gate i => exact Sum.inl i
    | block j k =>
        exact Sum.inr (⟨j, (MinRAFApprox.block_mem_canonicalRAF C j k).1 hr⟩, k)

/-- Canonical reactions are a disjoint sum of the gate indices and the
selected-set/block-coordinate pairs. -/
noncomputable def canonicalRAFEquiv (C : Finset (Fin n)) :
    {r // r ∈ MinRAFApprox.canonicalRAF (U := Fin m) (K := Fin M) C} ≃
      (Fin m) ⊕ ({j // j ∈ C} × Fin M) :=
  Equiv.ofBijective (canonicalRAFMap C) ⟨by
    intro a b hab
    apply Subtype.ext
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    cases a <;> cases b <;> simp [canonicalRAFMap] at hab ⊢
    all_goals exact hab,
    by
    intro s
    cases s with
    | inl i =>
        exact ⟨⟨MinRAFApprox.Reaction.gate i,
          MinRAFApprox.gate_mem_canonicalRAF C i⟩, by simp [canonicalRAFMap]⟩
    | inr jk =>
        rcases jk with ⟨⟨j, hj⟩, k⟩
        exact ⟨⟨MinRAFApprox.Reaction.block j k,
          (MinRAFApprox.block_mem_canonicalRAF C j k).2 hj⟩,
          by simp [canonicalRAFMap]⟩
  ⟩

/-- The mandatory gate backbone contributes `m`; every selected set contributes
exactly one block of `M` reactions. -/
theorem canonicalRAF_card (C : Finset (Fin n)) :
    (MinRAFApprox.canonicalRAF (U := Fin m) (K := Fin M) C).card =
      m + M * C.card := by
  classical
  calc
    (MinRAFApprox.canonicalRAF (U := Fin m) (K := Fin M) C).card =
        Fintype.card {r // r ∈ MinRAFApprox.canonicalRAF
          (U := Fin m) (K := Fin M) C} := (Fintype.card_coe _).symm
    _ = Fintype.card ((Fin m) ⊕ ({j // j ∈ C} × Fin M)) :=
      Fintype.card_congr (canonicalRAFEquiv C)
    _ = m + M * C.card := by
      simp [Fintype.card_coe, Nat.mul_comm]

end MinRAFApprox.SetCoverSource

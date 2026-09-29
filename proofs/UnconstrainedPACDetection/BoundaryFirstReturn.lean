module

public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic

@[expose] public section

namespace UnconstrainedPACDetection.BoundaryFirstReturn

theorem return_exists {X : Type*} [Fintype X] (p : Equiv.Perm X)
    (S : Set X) (a : X) (ha : a ∈ S) :
    ∃ n : ℕ, 0 < n ∧ (p : X → X)^[n] a ∈ S := by
  classical
  refine ⟨orderOf p, orderOf_pos p, ?_⟩
  have h := congrArg (fun q : Equiv.Perm X => q a) (pow_orderOf_eq_one p)
  have heq : (p : X → X)^[orderOf p] a = a := by
    simpa only [Equiv.Perm.coe_pow, Equiv.Perm.one_apply] using h
  rwa [heq]

noncomputable def length {X : Type*} [Fintype X] (p : Equiv.Perm X)
    (S : Set X) (a : S) : ℕ := by
  classical
  exact Nat.find (return_exists p S a.1 a.2)

theorem length_spec {X : Type*} [Fintype X] (p : Equiv.Perm X)
    (S : Set X) (a : S) :
    0 < length p S a ∧ (p : X → X)^[length p S a] a.1 ∈ S := by
  classical
  exact Nat.find_spec (return_exists p S a.1 a.2)

theorem no_internal_boundary {X : Type*} [Fintype X] (p : Equiv.Perm X)
    (S : Set X) (a : S) {i : ℕ} (hi : 0 < i) (hil : i < length p S a) :
    (p : X → X)^[i] a.1 ∉ S := by
  classical
  intro hm
  exact Nat.find_min (return_exists p S a.1 a.2) hil ⟨hi, hm⟩

/-- Prefixes before the first positive boundary return cannot intersect when
they start at different boundary points. -/
theorem prefixes_disjoint {X : Type*} [Fintype X] (p : Equiv.Perm X)
    (S : Set X) (a b : S) (hab : a ≠ b) {i j : ℕ}
    (hi : i < length p S a) (hj : j < length p S b) :
    (p : X → X)^[i] a.1 ≠ (p : X → X)^[j] b.1 := by
  intro h
  have habval : a.1 ≠ b.1 := fun hv => hab (Subtype.ext hv)
  rcases le_total i j with hij | hji
  · have he : i + (j - i) = j := by omega
    have hx : (p : X → X)^[i] ((p : X → X)^[j-i] b.1) =
        (p : X → X)^[i] a.1 := by
      rw [← Function.iterate_add_apply, he]
      exact h.symm
    have hy := (p.injective.iterate i) hx
    by_cases hz : j - i = 0
    · simp only [hz, Function.iterate_zero, id_eq] at hy
      exact habval hy.symm
    · exact no_internal_boundary p S b (by omega) (by omega) (hy.symm ▸ a.2)
  · have he : j + (i - j) = i := by omega
    have hx : (p : X → X)^[j] ((p : X → X)^[i-j] a.1) =
        (p : X → X)^[j] b.1 := by
      rw [← Function.iterate_add_apply, he]
      exact h
    have hy := (p.injective.iterate j) hx
    by_cases hz : i - j = 0
    · simp only [hz, Function.iterate_zero, id_eq] at hy
      exact habval hy
    · exact no_internal_boundary p S a (by omega) (by omega) (hy.symm ▸ b.2)

theorem prefix_injective {X : Type*} [Fintype X] (p : Equiv.Perm X)
    (S : Set X) (a : S) :
    Function.Injective (fun i : Fin (length p S a) => (p : X → X)^[i.1] a.1) := by
  intro i j h
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hc := Function.iterate_cancel p.injective h.symm
    exact no_internal_boundary p S a (by omega) (by omega) (hc.symm ▸ a.2)
  · have hc := Function.iterate_cancel p.injective h
    exact no_internal_boundary p S a (by omega) (by omega) (hc.symm ▸ a.2)

/-- Different boundary starts also have different first-return destinations. -/
theorem destinations_injective {X : Type*} [Fintype X] (p : Equiv.Perm X)
    (S : Set X) : Function.Injective
      (fun a : S => (p : X → X)^[length p S a] a.1) := by
  intro a b h
  by_contra hab
  have habval : a.1 ≠ b.1 := fun hv => hab (Subtype.ext hv)
  have ha := (length_spec p S a).1
  have hb := (length_spec p S b).1
  rcases le_total (length p S a) (length p S b) with hij | hji
  · have he : length p S a + (length p S b - length p S a) = length p S b := by omega
    have hx : (p : X → X)^[length p S a]
        ((p : X → X)^[length p S b - length p S a] b.1) =
        (p : X → X)^[length p S a] a.1 := by
      rw [← Function.iterate_add_apply, he]
      exact h.symm
    have hy := (p.injective.iterate (length p S a)) hx
    by_cases hz : length p S b - length p S a = 0
    · simp only [hz, Function.iterate_zero, id_eq] at hy
      exact habval hy.symm
    · exact no_internal_boundary p S b (by omega) (by omega) (hy.symm ▸ a.2)
  · have he : length p S b + (length p S a - length p S b) = length p S a := by omega
    have hx : (p : X → X)^[length p S b]
        ((p : X → X)^[length p S a - length p S b] a.1) =
        (p : X → X)^[length p S b] b.1 := by
      rw [← Function.iterate_add_apply, he]
      exact h
    have hy := (p.injective.iterate (length p S b)) hx
    by_cases hz : length p S a - length p S b = 0
    · simp only [hz, Function.iterate_zero, id_eq] at hy
      exact habval hy
    · exact no_internal_boundary p S a (by omega) (by omega) (hy.symm ▸ b.2)

end UnconstrainedPACDetection.BoundaryFirstReturn

module

public import proofs.UnconstrainedPACDetection.BoundarySegments

@[expose] public section

namespace UnconstrainedPACDetection.BoundaryFirstReturn

/-- Two crossed first-return segments support a potential constant along
internal transitions and with prescribed values at each sink predecessor.
The value is zero on every unused internal cycle. -/
theorem crossed_potential_exists {X : Type*} [Fintype X]
    (p : Equiv.Perm X) (S : Set X) (a b : S) (hab : a ≠ b)
    (ha : (p : X → X)^[length p S a] a.1 = b.1)
    (hb : (p : X → X)^[length p S b] b.1 = a.1) (u v : ℝ) :
    ∃ c : X → ℝ, c a.1 = u ∧ c b.1 = v ∧
      (∀ x, p x ∉ S → c (p x) = c x) ∧
      (∀ x, p x = a.1 → c x = v) ∧
      (∀ x, p x = b.1 → c x = u) ∧
      (∀ x, x ∉ segment p S a → x ∉ segment p S b → c x = 0) := by
  classical
  let c : X → ℝ := fun x => if x ∈ segment p S a then u
    else if x ∈ segment p S b then v else 0
  have hd := Set.disjoint_left.mp (segments_disjoint p S a b hab)
  have hcA (x : X) (hx : x ∈ segment p S a) : c x = u := by simp [c, hx]
  have hcB (x : X) (hx : x ∈ segment p S b) : c x = v := by
    have hn : x ∉ segment p S a := fun h => hd h hx
    simp [c, hx, hn]
  refine ⟨c, hcA _ (start_mem_segment p S a), hcB _ (start_mem_segment p S b),
    ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [c, segment_step_iff p S a x hx, segment_step_iff p S b x hx]
  · intro x hx
    exact hcB x (predecessor_mem_segment p S b x (hx.trans hb.symm))
  · intro x hx
    exact hcA x (predecessor_mem_segment p S a x (hx.trans ha.symm))
  · intro x hx hy
    simp [c, hx, hy]

end UnconstrainedPACDetection.BoundaryFirstReturn

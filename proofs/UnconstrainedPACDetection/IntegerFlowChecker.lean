module

public import proofs.UnconstrainedPACDetection.PACIntegerCertificate
public import proofs.UnconstrainedPACDetection.AdjugateFlow

@[expose] public section

/-! An executable algebraic checker with only an entity selection and one
integer flow. Binary serialization and machine-time bounds remain separate. -/

namespace UnconstrainedPACDetection

open ScaledInverseCertificate
variable {Entity Reaction : Type*}
  [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]

def ReversibleSource.IntegerFlowChecks (s : ReversibleSource Entity Reaction)
    (X : Finset Entity) (w : Reaction → ℤ) : Prop :=
  X.Nonempty ∧ (∀ r, w r ≠ 0 → s.sideAdmissible X r) ∧
    ∀ x ∈ X, 0 < ∑ r, s.netInt r x * w r

def ReversibleSource.checkIntegerFlow (s : ReversibleSource Entity Reaction)
    (X : Finset Entity) (w : Reaction → ℤ) : Bool :=
  decide (X.Nonempty ∧
    (∀ r, w r = 0 ∨ ((∃ x ∈ X, 0 < s.left r x) ∧
      ∃ x ∈ X, 0 < s.right r x)) ∧
    ∀ x ∈ X, 0 < ∑ r, s.netInt r x * w r)

omit [DecidableEq Reaction] in
theorem checkIntegerFlow_iff (s : ReversibleSource Entity Reaction)
    (X : Finset Entity) (w : Reaction → ℤ) :
    s.checkIntegerFlow X w = true ↔ s.IntegerFlowChecks X w := by
  simp [ReversibleSource.checkIntegerFlow, ReversibleSource.IntegerFlowChecks,
    ReversibleSource.sideAdmissible, or_iff_not_imp_left]

omit [DecidableEq Reaction] in
theorem integerFlowChecks_sound (s : ReversibleSource Entity Reaction)
    (X : Finset Entity) (w : Reaction → ℤ) (h : s.IntegerFlowChecks X w) :
    ∃ c, s.PAC c := by
  classical
  let R := Finset.univ.filter (fun r => w r ≠ 0)
  have hR : R.Nonempty := by
    by_contra hn
    have hz : ∀ r, w r = 0 := by
      intro r
      by_contra hw
      exact hn ⟨r, by simp [R, hw]⟩
    obtain ⟨x, hx⟩ := h.1
    have hp := h.2.2 x hx
    simp [hz] at hp
  apply (exists_pac_iff_exists_motif s).2
  refine ⟨(X, R), h.1, hR, ?_, (fun r => (w r : ℝ)), ?_, ?_⟩
  · intro r hr
    exact h.2.1 r (by simpa [R] using hr)
  · intro r hr
    have hz : w r = 0 := by simpa [R] using hr
    simp [hz]
  · intro x hx
    have hp := h.2.2 x hx
    have hreal : (0 : ℝ) < ∑ r, (s.netInt r x : ℝ) * (w r : ℝ) := by
      exact_mod_cast hp
    simpa [ReversibleSource.netInt, ReversibleSource.net] using hreal

def ReversibleSource.minorFlow (s : ReversibleSource Entity Reaction)
    (c : Candidate Entity Reaction) (e : ↥c.2 ≃ ↥c.1) : Reaction → ℤ :=
  fun r => if hr : r ∈ c.2 then adjugateFlow (s.certificateMatrix c e) ⟨r, hr⟩ else 0

omit [Fintype Entity] in
theorem minorFlow_checks (s : ReversibleSource Entity Reaction)
    (c : Candidate Entity Reaction) (e : ↥c.2 ≃ ↥c.1) (h : s.SquareMinor c) :
    s.IntegerFlowChecks c.1 (s.minorFlow c e) := by
  classical
  let A := s.certificateMatrix c e
  have hd : A.det ≠ 0 := (exists_certificate_iff A).1
    ((real_rows_iff_certificate A).1 ((certificateMatrix_independence s c e).1 h.2.2.2.2))
  let w := s.minorFlow c e
  change s.IntegerFlowChecks c.1 w
  refine ⟨h.1, ?_, ?_⟩
  · intro r hr
    have hm : r ∈ c.2 := by by_contra hn; exact hr (by simp [w, ReversibleSource.minorFlow, hn])
    exact h.2.2.1 r hm
  · intro x hx
    have heq : ∑ r, s.netInt r x * w r = A.det * A.det := by
      calc
        ∑ r, s.netInt r x * w r = ∑ r ∈ c.2, s.netInt r x * w r := by
          symm
          apply Finset.sum_subset (Finset.subset_univ c.2)
          intro r _ hr
          simp [w, ReversibleSource.minorFlow, hr]
        _ = ∑ r : ↥c.2, A r (e.symm ⟨x, hx⟩) * adjugateFlow A r := by
          rw [← Finset.sum_finset_coe]
          simp [A, ReversibleSource.certificateMatrix, w, ReversibleSource.minorFlow]
        _ = _ := adjugateFlow_balance A (e.symm ⟨x, hx⟩)
    rw [heq]
    exact mul_self_pos.mpr hd

omit [Fintype Entity] in
theorem squareMinor_integerFlow (s : ReversibleSource Entity Reaction)
    (c : Candidate Entity Reaction) (h : s.SquareMinor c) :
    ∃ w, s.IntegerFlowChecks c.1 w := by
  obtain ⟨e⟩ : Nonempty (↥c.2 ≃ ↥c.1) := Fintype.card_eq.mp (by simpa using h.2.2.2.1.symm)
  exact ⟨s.minorFlow c e, minorFlow_checks s c e h⟩

theorem exists_pac_iff_checkIntegerFlow (s : ReversibleSource Entity Reaction) :
    (∃ c, s.PAC c) ↔ ∃ X w, s.checkIntegerFlow X w = true := by
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := (exists_pac_iff_exists_squareMinor s).1 hp
    obtain ⟨w, hw⟩ := squareMinor_integerFlow s c hc
    exact ⟨c.1, w, (checkIntegerFlow_iff s c.1 w).2 hw⟩
  · rintro ⟨X, w, hw⟩
    exact integerFlowChecks_sound s X w ((checkIntegerFlow_iff s X w).1 hw)

end UnconstrainedPACDetection

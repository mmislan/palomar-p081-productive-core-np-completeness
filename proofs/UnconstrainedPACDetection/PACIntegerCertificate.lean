module

public import proofs.UnconstrainedPACDetection.SquareMinor
public import proofs.UnconstrainedPACDetection.ScaledInverseBounds

@[expose] public section

/-! A source-faithful bounded integer certificate: both literal sides are
checked, including catalysts whose net coefficient is zero. -/

namespace UnconstrainedPACDetection

open ScaledInverseCertificate

variable {Entity Reaction : Type*}
  [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]

def ReversibleSource.netInt (s : ReversibleSource Entity Reaction)
    (r : Reaction) (x : Entity) : ℤ := (s.right r x : ℤ) - (s.left r x : ℤ)

def ReversibleSource.certificateMatrix (s : ReversibleSource Entity Reaction)
    (c : Candidate Entity Reaction) (e : ↥c.2 ≃ ↥c.1) : Matrix ↥c.2 ↥c.2 ℤ :=
  fun r j => s.netInt r.1 (e j).1

omit [Fintype Entity] [DecidableEq Entity] [Fintype Reaction] [DecidableEq Reaction] in
theorem certificateMatrix_independence (s : ReversibleSource Entity Reaction)
    (c : Candidate Entity Reaction) (e : ↥c.2 ≃ ↥c.1) :
    LinearIndependent ℝ (fun r : ↥c.2 => fun x : ↥c.1 => s.net r.1 x.1) ↔
      LinearIndependent ℝ (fun i j => (s.certificateMatrix c e i j : ℝ)) := by
  let L : (↥c.1 → ℝ) →ₗ[ℝ] (↥c.2 → ℝ) := LinearMap.funLeft ℝ ℝ e
  have hinj : Function.Injective L := by
    intro f g h
    funext x
    have hx := congrFun h (e.symm x)
    simpa [L, LinearMap.funLeft_apply] using hx
  have hiff := L.linearIndependent_iff_of_injOn
    (v := fun r : ↥c.2 => fun x : ↥c.1 => s.net r.1 x.1) hinj.injOn
  have hfamily :
      (fun i j => (s.certificateMatrix c e i j : ℝ)) =
        (fun r => L (fun x : ↥c.1 => s.net r.1 x.1)) := by
    funext i j
    simp [L, ReversibleSource.certificateMatrix, ReversibleSource.netInt,
      ReversibleSource.net]
  rw [hfamily]
  simpa [Function.comp_def] using hiff.symm

def ReversibleSource.IntegerCertificate (s : ReversibleSource Entity Reaction)
    (c : Candidate Entity Reaction) (H : ℤ) : Prop :=
  c.1.Nonempty ∧ c.2.Nonempty ∧
    (∀ r ∈ c.2, s.sideAdmissible c.1 r) ∧
    ∃ e : ↥c.2 ≃ ↥c.1, ∃ d B,
      Accepts (s.certificateMatrix c e) d B ∧
      |d| ≤ heightBound (n := ↥c.2) H ∧
      ∀ i j, |B i j| ≤ heightBound (n := ↥c.2) H

omit [Fintype Entity] [Fintype Reaction] in
theorem squareMinor_iff_integerCertificate (s : ReversibleSource Entity Reaction)
    (c : Candidate Entity Reaction) (H : ℤ) (hH : 1 ≤ H)
    (hs : ∀ r x, |s.netInt r x| ≤ H) :
    s.SquareMinor c ↔ s.IntegerCertificate c H := by
  constructor
  · rintro ⟨hx, hr, ha, hcard, hi⟩
    obtain ⟨e⟩ : Nonempty (↥c.2 ≃ ↥c.1) := Fintype.card_eq.mp (by simpa using hcard.symm)
    refine ⟨hx, hr, ha, e, ?_⟩
    apply (exists_bounded_certificate_iff (s.certificateMatrix c e) H hH
      (fun r j => hs r.1 (e j).1)).2
    exact (certificateMatrix_independence s c e).1 hi
  · rintro ⟨hx, hr, ha, e, hc⟩
    refine ⟨hx, hr, ha, ?_, ?_⟩
    · simpa using (Fintype.card_congr e).symm
    · apply (certificateMatrix_independence s c e).2
      exact (exists_bounded_certificate_iff (s.certificateMatrix c e) H hH
        (fun r j => hs r.1 (e j).1)).1 hc

theorem exists_pac_iff_integerCertificate (s : ReversibleSource Entity Reaction)
    (H : ℤ) (hH : 1 ≤ H) (hs : ∀ r x, |s.netInt r x| ≤ H) :
    (∃ c, s.PAC c) ↔ ∃ c, s.IntegerCertificate c H := by
  rw [exists_pac_iff_exists_squareMinor]
  exact exists_congr fun c => squareMinor_iff_integerCertificate s c H hH hs

end UnconstrainedPACDetection

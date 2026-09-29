module

public import proofs.UnconstrainedPACDetection.LinkagePathUnion
public import proofs.UnconstrainedPACDetection.LinkageNormalizedKernel
public import proofs.UnconstrainedPACDetection.LinkagePACConverse

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource.PathUnion

variable {V E : Type*} [DecidableEq E] [DecidableEq V] {D : Network V E}
variable (P : ArcPath D false false) (R : ArcPath D true true)

theorem independent : LinearIndependent ℝ
    (fun r : rows P R => fun e : entities P R => (matrix D r.1 e.1 : ℝ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro f hf r
  let x : Bool ⊕ V → ℝ := fun v => if h : v ∈ rows P R then f ⟨v, h⟩ else 0
  have hx (v : rows P R) : x v.1 = f v := by simp [x]
  have heq (e : E) (he : e ∈ entities P R) :
      headPotential x (D.head e) = tailPotential x (D.tail e) := by
    apply normalized_endpoint_equation D x e
    have hz : (∑ v ∈ rows P R, x v * (matrix D v e : ℝ)) = 0 := by
      rw [← Finset.sum_coe_sort (rows P R) (fun v => x v * (matrix D v e : ℝ))]
      have h := congrFun hf ⟨e, he⟩
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hx] using h
    exact (weighted_column_sum D (rows P R) x e
      (endpoint_rows_mem P R he).1 (endpoint_rows_mem P R he).2).symm.trans hz
  have hi (z : V) : tailPotential x (Sum.inr z) = headPotential x (Sum.inr z) := rfl
  obtain ⟨hA, hP⟩ := P.transport (tailPotential x) (headPotential x)
    (fun i => heq _ (arcP_mem P R i)) hi
  obtain ⟨hB, hR⟩ := R.transport (tailPotential x) (headPotential x)
    (fun i => heq _ (arcR_mem P R i)) hi
  have hA' : -x (Sum.inl true) = x (Sum.inl false) := hA
  have hB' : 2 * x (Sum.inl true) = -x (Sum.inl false) / 2 := hB
  have hs : x (Sum.inl false) = 0 := by linarith
  have ht : x (Sum.inl true) = 0 := by linarith
  rw [← hx r]
  cases hr : r.1 with
  | inl b => cases b
             · exact hs
             · exact ht
  | inr z =>
    obtain ⟨e, he, htail⟩ := Finset.mem_image.mp r.2
    rw [hr] at htail
    rcases (mem_entities P R e).mp he with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · simpa only [htail, tailPotential, hs] using hP i
    · simpa only [htail, tailPotential, hs, neg_zero, zero_div] using hR i

theorem mixed_minor [Fintype V] [Fintype E]
    (hdis : Disjoint P.vertices R.vertices) :
    (source D).MixedSquareMinor (entities P R, rows P R) := by
  refine ⟨⟨P.arcs ⟨0, P.positive⟩, arcP_mem P R _⟩,
    ⟨Sum.inl false, source_mem P R⟩, ?_, card_eq P R hdis, ?_⟩
  · intro r hr
    obtain ⟨⟨e, he, hn⟩, f, hf, hp⟩ := mixed P R r hr
    constructor
    · refine ⟨e, he, ?_⟩
      rw [source_net]
      exact_mod_cast hn
    · refine ⟨f, hf, ?_⟩
      rw [source_net]
      exact_mod_cast hp
  · simpa only [source_net] using independent P R

end PathUnion

theorem linkage_implies_pac {V E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (D : Network V E) (P : ArcPath D false false) (R : ArcPath D true true)
    (hdis : Disjoint P.vertices R.vertices) : ∃ candidate, (source D).PAC candidate :=
  (exists_pac_iff_exists_mixedSquareMinor (source D) (source_nonambiguous D)).mpr
    ⟨_, PathUnion.mixed_minor P R hdis⟩

theorem pac_iff_linkage {V E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (D : Network V E) :
    (∃ candidate, (source D).PAC candidate) ↔
      ∃ (P : ArcPath D false false) (R : ArcPath D true true),
        Disjoint P.vertices R.vertices := by
  constructor
  · exact pac_implies_linkage D
  · rintro ⟨P, R, h⟩
    exact linkage_implies_pac D P R h

end UnconstrainedPACDetection.DirectedLinkageSource

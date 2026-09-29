module

public import proofs.UnconstrainedPACDetection.LinkageDesiredExtraction

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

def Network.restrictEntities {V E : Type*} (D : Network V E) (es : Finset E) :
    Network V es where
  tail e := D.tail e.1
  head e := D.head e.1
  noLoop e v := D.noLoop e.1 v

theorem matrix_restrictEntities {V E : Type*} [DecidableEq V]
    (D : Network V E) (es : Finset E) (r : Bool ⊕ V) (e : es) :
    matrix (D.restrictEntities es) r e = matrix D r e.1 := rfl

def ArcPath.liftRestriction {V E : Type*} {D : Network V E} {es : Finset E}
    {s t : Bool} (P : ArcPath (D.restrictEntities es) s t) : ArcPath D s t where
  length := P.length
  positive := P.positive
  arcs i := (P.arcs i).1
  start := P.start
  finish := P.finish
  consecutive := P.consecutive
  internal := P.internal
  tail_injective := P.tail_injective

theorem subtype_filter_card {X : Type*} (s : Finset X) (p : X → Prop)
    [DecidablePred p] :
    (Finset.univ.filter (fun x : s => p x.1)).card = (s.filter p).card := by
  classical
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨x.2, (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x, (Finset.mem_filter.mp hx).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩, rfl⟩

/-- The converse is for every literal PAC and every accepting projection,
not just the intended full matrix or a preselected support. -/
theorem pac_implies_linkage {V E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (D : Network V E) (hpac : ∃ candidate, (source D).PAC candidate) :
    ∃ (P : ArcPath D false false) (R : ArcPath D true true),
      Disjoint P.vertices R.vertices := by
  classical
  obtain ⟨⟨es, rs⟩, _, hrs, hm, hcard, hind⟩ :=
    (exists_pac_iff_exists_mixedSquareMinor (source D) (source_nonambiguous D)).mp hpac
  let Dr := D.restrictEntities es
  let A : rs → es → ℝ := fun r e => (matrix D r.1 e.1 : ℝ)
  have hmA : ∀ r : rs, (∃ e : es, A r e < 0) ∧ ∃ e : es, 0 < A r e := by
    intro r
    obtain ⟨⟨e, he, hen⟩, f, hf, hfp⟩ := hm r.1 r.2
    exact ⟨⟨⟨e, he⟩, by simpa only [source_net] using hen⟩,
      ⟨⟨f, hf⟩, by simpa only [source_net] using hfp⟩⟩
  have hcA : ∀ e : es, (Finset.univ.filter (fun r : rs => A r e ≠ 0)).card ≤ 2 := by
    intro e
    dsimp only [A]
    rw [subtype_filter_card rs (fun r => (matrix D r e.1 : ℝ) ≠ 0)]
    calc
      _ ≤ (Finset.univ.filter (fun r => (matrix D r e.1 : ℝ) ≠ 0)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ rs))
      _ = 2 := by simpa only [Int.cast_ne_zero] using column_degree_two D e.1
  have hsize : Fintype.card rs = Fintype.card es := by simpa using hcard.symm
  obtain ⟨hrowA, hcolA⟩ := DegreeTwoSaturation.mixed_square_degrees_two A hsize hmA hcA
  have hr : ∀ r ∈ rs,
      (Finset.univ.filter (fun e : es => matrix Dr r e ≠ 0)).card ≤ 2 := by
    intro r hr
    have h := hrowA ⟨r, hr⟩
    have he : (Finset.univ.filter (fun e : es => matrix Dr r e ≠ 0)).card = 2 := by
      have hfilter :
          Finset.univ.filter (fun e : es => matrix Dr r e ≠ 0) =
            Finset.univ.filter (fun e : es => A ⟨r, hr⟩ e ≠ 0) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ,
          true_and, A, Dr, matrix_restrictEntities, Int.cast_ne_zero]
        constructor
        · intro he
          exact (Finset.mem_filter.mp he).2
        · intro he
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩
      rw [hfilter]
      exact h
    omega
  have hc : ∀ e : es, (rs.filter (fun r => matrix Dr r e ≠ 0)).card = 2 := by
    intro e
    have h := hcolA e
    dsimp only [A] at h
    rw [subtype_filter_card rs (fun r => (matrix D r e.1 : ℝ) ≠ 0)] at h
    have hfilter :
        rs.filter (fun r => matrix Dr r e ≠ 0) =
          rs.filter (fun r => (matrix D r e.1 : ℝ) ≠ 0) := by
      ext r
      simp only [Finset.mem_filter, Dr, matrix_restrictEntities, Int.cast_ne_zero]
      constructor
      · intro hr
        exact Finset.mem_filter.mp hr
      · intro hr
        exact Finset.mem_filter.mpr hr
    rw [hfilter]
    exact h
  have hmix : ∀ r ∈ rs,
      (∃ e : es, matrix Dr r e < 0) ∧ ∃ e : es, 0 < matrix Dr r e := by
    intro r hr
    obtain ⟨⟨e, he⟩, f, hf⟩ := hmA ⟨r, hr⟩
    constructor
    · refine ⟨e, ?_⟩
      change matrix D r e.1 < 0
      change (matrix D r e.1 : ℝ) < 0 at he
      exact_mod_cast he
    · refine ⟨f, ?_⟩
      change 0 < matrix D r f.1
      change (0 : ℝ) < (matrix D r f.1 : ℝ) at hf
      exact_mod_cast hf
  have hlin : LinearIndependent ℝ (fun r : rs => fun e : es => (matrix Dr r.1 e : ℝ)) := by
    simpa only [source_net, Dr, matrix_restrictEntities] using hind
  obtain ⟨P, R, hdis⟩ := independent_selection_linkage Dr rs hrs hr hmix hc hlin
  exact ⟨P.liftRestriction, R.liftRestriction, hdis⟩

end UnconstrainedPACDetection.DirectedLinkageSource

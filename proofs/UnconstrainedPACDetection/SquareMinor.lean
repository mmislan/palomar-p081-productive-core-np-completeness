module

public import proofs.UnconstrainedPACDetection.CoreWitness
public import proofs.UnconstrainedPACDetection.FixedSupport
public import proofs.UnconstrainedPACDetection.MotifDescent
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section

/-!
An exact algebraic normal form for unconstrained PAC detection.  A candidate
is a square minor when its reactions are side-admissible, its entity and
reaction sets have the same cardinality, and its restricted net columns are
linearly independent.  Such a minor is automatically productive: its column
map is an isomorphism and therefore maps some signed flow to the all-ones
vector.
-/

namespace UnconstrainedPACDetection

variable {Entity Reaction : Type*}
  [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]

def ReversibleSource.SquareMinor
    (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) : Prop :=
  candidate.1.Nonempty ∧
    candidate.2.Nonempty ∧
    (∀ reaction ∈ candidate.2,
      source.sideAdmissible candidate.1 reaction) ∧
    candidate.1.card = candidate.2.card ∧
    LinearIndependent ℝ (fun reaction : ↥candidate.2 =>
      fun entity : ↥candidate.1 => source.net reaction.1 entity.1)

omit [DecidableEq Reaction] in
theorem squareMinor_productive
    (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction)
    (hsquare : source.SquareMinor candidate) :
    source.Productive candidate.1 candidate.2 := by
  classical
  let columns : ↥candidate.2 → (↥candidate.1 → ℝ) := fun reaction entity =>
    source.net reaction.1 entity.1
  let combination : (↥candidate.2 → ℝ) →ₗ[ℝ] (↥candidate.1 → ℝ) :=
    Fintype.linearCombination ℝ columns
  have hinjective : Function.Injective combination := by
    exact hsquare.2.2.2.2.fintypeLinearCombination_injective
  have hdimension : Module.finrank ℝ (↥candidate.2 → ℝ) =
      Module.finrank ℝ (↥candidate.1 → ℝ) := by
    simp [hsquare.2.2.2.1]
  have hsurjective : Function.Surjective combination :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimension).mp
      hinjective
  obtain ⟨coeff, hcoeff⟩ := hsurjective (fun _ => (1 : ℝ))
  let flow : Reaction → ℝ := Subtype.val.extend coeff 0
  refine ⟨flow, ?_, ?_⟩
  · intro reaction hreaction
    have hnotRange : ¬ ∃ selected : ↥candidate.2, selected.1 = reaction := by
      intro hexists
      rcases hexists with ⟨selected, hselected⟩
      exact hreaction (hselected ▸ selected.2)
    exact Function.extend_apply' (f := fun selected : ↥candidate.2 => selected.1)
      coeff (0 : Reaction → ℝ) reaction hnotRange
  · intro entity hentity
    have hcoordinate := congrFun hcoeff ⟨entity, hentity⟩
    simp only [combination, Fintype.linearCombination_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] at hcoordinate
    have hrestricted : candidate.2.sum (fun reaction =>
        source.net reaction entity * flow reaction) = 1 := by
      rw [← Finset.sum_finset_coe]
      simpa [columns, flow, Subtype.val_injective.extend_apply, mul_comm] using
        hcoordinate
    have hall : Finset.univ.sum (fun reaction =>
        source.net reaction entity * flow reaction) = 1 := by
      calc
        Finset.univ.sum (fun reaction =>
            source.net reaction entity * flow reaction) =
            candidate.2.sum (fun reaction =>
              source.net reaction entity * flow reaction) := by
                symm
                apply Finset.sum_subset (Finset.subset_univ candidate.2)
                intro reaction _huniv hnotSelected
                simp [flow, hnotSelected]
        _ = 1 := hrestricted
    rw [hall]
    exact zero_lt_one

theorem exists_pac_iff_exists_squareMinor
    (source : ReversibleSource Entity Reaction) :
    (∃ candidate, source.PAC candidate) ↔
      ∃ candidate, source.SquareMinor candidate := by
  constructor
  · rintro ⟨candidate, hPAC⟩
    exact ⟨candidate, hPAC.1.1, hPAC.1.2.1, hPAC.1.2.2.1,
      pac_card_entities_eq_reactions source candidate hPAC,
      pac_net_columns_linearIndependent source candidate hPAC⟩
  · rintro ⟨candidate, hsquare⟩
    apply (exists_pac_iff_exists_motif source).2
    exact ⟨candidate, hsquare.1, hsquare.2.1, hsquare.2.2.1,
      squareMinor_productive source candidate hsquare⟩

def ReversibleSource.FullRankSupport
    (source : ReversibleSource Entity Reaction) (entities : Finset Entity) : Prop :=
  entities.Nonempty ∧
    Submodule.span ℝ (Set.range (fun reaction : ↥(source.fullAdmissible entities) =>
      fun entity : ↥entities => source.net reaction.1 entity.1)) = ⊤

theorem exists_pac_iff_exists_fullRankSupport
    (source : ReversibleSource Entity Reaction) :
    (∃ candidate, source.PAC candidate) ↔
      ∃ entities, source.FullRankSupport entities := by
  classical
  constructor
  · intro hexists
    rcases (exists_pac_iff_exists_squareMinor source).1 hexists with
      ⟨candidate, hsquare⟩
    let smallColumns : ↥candidate.2 → (↥candidate.1 → ℝ) := fun reaction entity =>
      source.net reaction.1 entity.1
    let largeColumns : ↥(source.fullAdmissible candidate.1) →
        (↥candidate.1 → ℝ) := fun reaction entity =>
      source.net reaction.1 entity.1
    let smallCombination : (↥candidate.2 → ℝ) →ₗ[ℝ]
        (↥candidate.1 → ℝ) := Fintype.linearCombination ℝ smallColumns
    have hinjective : Function.Injective smallCombination := by
      exact hsquare.2.2.2.2.fintypeLinearCombination_injective
    have hdimension : Module.finrank ℝ (↥candidate.2 → ℝ) =
        Module.finrank ℝ (↥candidate.1 → ℝ) := by
      simp [hsquare.2.2.2.1]
    have hsurjective : Function.Surjective smallCombination :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimension).mp
        hinjective
    have hsmallSpan : Submodule.span ℝ (Set.range smallColumns) = ⊤ :=
      (span_range_eq_top_iff_surjective_fintypeLinearCombination
        ℝ smallColumns).2 hsurjective
    have hrange : Set.range smallColumns ⊆ Set.range largeColumns := by
      rintro vector ⟨reaction, rfl⟩
      have hfull : reaction.1 ∈ source.fullAdmissible candidate.1 :=
        (mem_fullAdmissible_iff source candidate.1 reaction.1).2
          (hsquare.2.2.1 reaction.1 reaction.2)
      exact ⟨⟨reaction.1, hfull⟩, rfl⟩
    refine ⟨candidate.1, hsquare.1, ?_⟩
    apply top_unique
    rw [← hsmallSpan]
    exact Submodule.span_mono hrange
  · rintro ⟨entities, hentities, hspan⟩
    apply (exists_pac_iff_exists_motif source).2
    let columns : ↥(source.fullAdmissible entities) → (↥entities → ℝ) :=
      fun reaction entity => source.net reaction.1 entity.1
    let combination : (↥(source.fullAdmissible entities) → ℝ) →ₗ[ℝ]
        (↥entities → ℝ) := Fintype.linearCombination ℝ columns
    have hsurjective : Function.Surjective combination :=
      (span_range_eq_top_iff_surjective_fintypeLinearCombination
        ℝ columns).1 hspan
    obtain ⟨coeff, hcoeff⟩ := hsurjective (fun _ => (1 : ℝ))
    have hreactions : (source.fullAdmissible entities).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have : Nonempty ↥entities := Finset.nonempty_coe_sort.mpr hentities
      have hrangeEmpty : Set.range columns = ∅ := by
        ext vector
        constructor
        · intro hvector
          rcases hvector with ⟨reaction, _hvector⟩
          have : reaction.1 ∈ (∅ : Finset Reaction) := by
            simpa [hempty] using reaction.2
          simp at this
        · simp
      change Submodule.span ℝ (Set.range columns) = ⊤ at hspan
      rw [hrangeEmpty, Submodule.span_empty] at hspan
      exact bot_ne_top hspan
    let flow : Reaction → ℝ := Subtype.val.extend coeff 0
    refine ⟨(entities, source.fullAdmissible entities), hentities, hreactions,
      ?_, ⟨flow, ?_, ?_⟩⟩
    · intro reaction hreaction
      exact (mem_fullAdmissible_iff source entities reaction).1 hreaction
    · intro reaction hreaction
      have hnotRange : ¬ ∃ selected : ↥(source.fullAdmissible entities),
          selected.1 = reaction := by
        intro hexists
        rcases hexists with ⟨selected, hselected⟩
        exact hreaction (hselected ▸ selected.2)
      exact Function.extend_apply'
        (f := fun selected : ↥(source.fullAdmissible entities) => selected.1)
        coeff (0 : Reaction → ℝ) reaction hnotRange
    · intro entity hentity
      have hcoordinate := congrFun hcoeff ⟨entity, hentity⟩
      simp only [combination, Fintype.linearCombination_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul] at hcoordinate
      have hrestricted : (source.fullAdmissible entities).sum (fun reaction =>
          source.net reaction entity * flow reaction) = 1 := by
        rw [← Finset.sum_finset_coe]
        simpa [columns, flow, Subtype.val_injective.extend_apply, mul_comm] using
          hcoordinate
      have hall : Finset.univ.sum (fun reaction =>
          source.net reaction entity * flow reaction) = 1 := by
        calc
          Finset.univ.sum (fun reaction =>
              source.net reaction entity * flow reaction) =
              (source.fullAdmissible entities).sum (fun reaction =>
                source.net reaction entity * flow reaction) := by
                  symm
                  apply Finset.sum_subset
                    (Finset.subset_univ (source.fullAdmissible entities))
                  intro reaction _huniv hnotSelected
                  simp [flow, hnotSelected]
          _ = 1 := hrestricted
      rw [hall]
      exact zero_lt_one

end UnconstrainedPACDetection

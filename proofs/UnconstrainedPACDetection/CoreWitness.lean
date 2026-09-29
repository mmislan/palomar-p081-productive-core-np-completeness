module

public import proofs.UnconstrainedPACDetection.Motif
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section

/-!
The first source-faithful child-selection seam: a witness on an inclusion-
minimal core cannot assign zero flux to a selected reaction.  Consequently
every selected reversible reaction has a definite orientation in every
productive witness.
-/

namespace UnconstrainedPACDetection

variable {Entity Reaction : Type*}
  [Fintype Entity] [DecidableEq Entity]
  [Fintype Reaction] [DecidableEq Reaction]

omit [Fintype Entity] in
theorem pac_flow_ne_zero (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) (hPAC : source.PAC candidate)
    (flow : Reaction → ℝ)
    (hsupport : ∀ reaction, reaction ∉ candidate.2 → flow reaction = 0)
    (hpositive : ∀ entity ∈ candidate.1,
      0 < Finset.univ.sum (fun reaction =>
        source.net reaction entity * flow reaction)) :
    ∀ reaction ∈ candidate.2, flow reaction ≠ 0 := by
  classical
  intro reaction hreaction hzero
  have hsome : ∃ other, flow other ≠ 0 := by
    by_contra hallzero
    push Not at hallzero
    rcases hPAC.1.1 with ⟨entity, hentity⟩
    have hpos := hpositive entity hentity
    simp [hallzero] at hpos
  rcases hsome with ⟨other, hother⟩
  have hotherMem : other ∈ candidate.2 := by
    by_contra hnotmem
    exact hother (hsupport other hnotmem)
  have hotherNe : other ≠ reaction := by
    intro heq
    exact hother (heq ▸ hzero)
  let smaller : Candidate Entity Reaction :=
    (candidate.1, candidate.2.erase reaction)
  have hsmallerMotif : source.Motif smaller := by
    refine ⟨hPAC.1.1, ?_, ?_, ?_⟩
    · exact ⟨other, Finset.mem_erase.mpr ⟨hotherNe, hotherMem⟩⟩
    · intro selected hselected
      exact hPAC.1.2.2.1 selected (Finset.mem_of_mem_erase hselected)
    · refine ⟨flow, ?_, hpositive⟩
      intro selected hselected
      by_cases heq : selected = reaction
      · simpa [heq] using hzero
      · apply hsupport selected
        intro hselectedOriginal
        exact hselected (Finset.mem_erase.mpr ⟨heq, hselectedOriginal⟩)
  have hsmaller : smaller < candidate := by
    change smaller ≤ candidate ∧ ¬ candidate ≤ smaller
    constructor
    · constructor
      · exact le_rfl
      · exact Finset.erase_subset reaction candidate.2
    · intro hback
      have := hback.2 hreaction
      change reaction ∈ candidate.2.erase reaction at this
      exact (Finset.mem_erase.mp this).1 rfl
  exact hPAC.2 hsmaller hsmallerMotif

omit [Fintype Entity] [DecidableEq Reaction] in
theorem pac_entity_has_critical_reaction
    (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) (hPAC : source.PAC candidate) :
    ∀ entity ∈ candidate.1, ∃ reaction ∈ candidate.2,
      ¬ source.sideAdmissible (candidate.1.erase entity) reaction := by
  classical
  intro entity hentity
  by_contra hcritical
  push Not at hcritical
  let smaller : Candidate Entity Reaction :=
    (candidate.1.erase entity, candidate.2)
  have hsmallerMotif : source.Motif smaller := by
    refine ⟨?_, hPAC.1.2.1, ?_, ?_⟩
    · rcases hPAC.1.2.1 with ⟨reaction, hreaction⟩
      rcases (hcritical reaction hreaction).1 with
        ⟨other, hother, _hleft⟩
      exact ⟨other, hother⟩
    · intro reaction hreaction
      exact hcritical reaction hreaction
    · rcases hPAC.1.2.2.2 with ⟨flow, hsupport, hpositive⟩
      refine ⟨flow, hsupport, ?_⟩
      intro other hother
      exact hpositive other (Finset.mem_of_mem_erase hother)
  have hsmaller : smaller < candidate := by
    change smaller ≤ candidate ∧ ¬ candidate ≤ smaller
    constructor
    · constructor
      · exact Finset.erase_subset entity candidate.1
      · exact le_rfl
    · intro hback
      have := hback.1 hentity
      change entity ∈ candidate.1.erase entity at this
      exact (Finset.mem_erase.mp this).1 rfl
  exact hPAC.2 hsmaller hsmallerMotif

/-! Witness-dependent orientations for the stronger child-selection seam. -/

noncomputable def ReversibleSource.orientedReactants
    (source : ReversibleSource Entity Reaction) (entities : Finset Entity)
    (flow : Reaction → ℝ) (reaction : Reaction) : Finset Entity :=
  if 0 < flow reaction then
    entities.filter (fun entity => 0 < source.left reaction entity)
  else
    entities.filter (fun entity => 0 < source.right reaction entity)

noncomputable def ReversibleSource.orientedProducts
    (source : ReversibleSource Entity Reaction) (entities : Finset Entity)
    (flow : Reaction → ℝ) (reaction : Reaction) : Finset Entity :=
  if 0 < flow reaction then
    entities.filter (fun entity => 0 < source.right reaction entity)
  else
    entities.filter (fun entity => 0 < source.left reaction entity)

omit [Fintype Entity] [Fintype Reaction] [DecidableEq Reaction] in
private theorem positive_filter_eq_singleton_of_erase_none
    (entities : Finset Entity) (entity : Entity) (coeff : Entity → ℕ)
    (hentity : entity ∈ entities)
    (hsome : ∃ other ∈ entities, 0 < coeff other)
    (herase : ¬ ∃ other ∈ entities.erase entity, 0 < coeff other) :
    entities.filter (fun other => 0 < coeff other) = {entity} := by
  ext other
  constructor
  · intro hother
    have hmem := (Finset.mem_filter.mp hother).1
    have hpos := (Finset.mem_filter.mp hother).2
    have heq : other = entity := by
      by_contra hne
      exact herase ⟨other, Finset.mem_erase.mpr ⟨hne, hmem⟩, hpos⟩
    simp [heq]
  · intro hother
    have heq : other = entity := by simpa using hother
    subst other
    have hpos : 0 < coeff entity := by
      rcases hsome with ⟨other, hotherMem, hotherPos⟩
      by_contra hnot
      have hne : other ≠ entity := by
        intro heq
        subst other
        exact hnot hotherPos
      exact herase ⟨other, Finset.mem_erase.mpr ⟨hne, hotherMem⟩, hotherPos⟩
    exact Finset.mem_filter.mpr ⟨hentity, hpos⟩

omit [Fintype Entity] [Fintype Reaction] [DecidableEq Reaction] in
private theorem net_mul_nonpos_of_orientedProducts_eq_singleton
    (source : ReversibleSource Entity Reaction) (entities : Finset Entity)
    (flow : Reaction → ℝ) (reaction : Reaction) (entity other : Entity)
    (hflow : flow reaction ≠ 0)
    (hproducts : source.orientedProducts entities flow reaction = {entity})
    (hother : other ∈ entities.erase entity) :
    source.net reaction other * flow reaction ≤ 0 := by
  have hotherNe : other ≠ entity := (Finset.mem_erase.mp hother).1
  have hotherMem : other ∈ entities := Finset.mem_of_mem_erase hother
  by_cases hpositive : 0 < flow reaction
  · have hrightZero : source.right reaction other = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hright
      have hmem : other ∈ source.orientedProducts entities flow reaction := by
        simp [ReversibleSource.orientedProducts, hpositive, hotherMem, hright]
      rw [hproducts] at hmem
      exact hotherNe (by simpa using hmem)
    simp only [ReversibleSource.net, hrightZero, Nat.cast_zero, zero_sub]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Nat.cast_nonneg _)) (le_of_lt hpositive)
  · have hnegative : flow reaction < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpositive) hflow
    have hleftZero : source.left reaction other = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hleft
      have hmem : other ∈ source.orientedProducts entities flow reaction := by
        simp [ReversibleSource.orientedProducts, hpositive, hotherMem, hleft]
      rw [hproducts] at hmem
      exact hotherNe (by simpa using hmem)
    simp only [ReversibleSource.net, hleftZero, Nat.cast_zero, sub_zero]
    exact mul_nonpos_of_nonneg_of_nonpos
      (Nat.cast_nonneg _) (le_of_lt hnegative)

omit [Fintype Entity] in
theorem pac_entity_is_sole_oriented_reactant
    (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) (hPAC : source.PAC candidate)
    (flow : Reaction → ℝ)
    (hsupport : ∀ reaction, reaction ∉ candidate.2 → flow reaction = 0)
    (hpositive : ∀ entity ∈ candidate.1,
      0 < Finset.univ.sum (fun reaction =>
        source.net reaction entity * flow reaction)) :
    ∀ entity ∈ candidate.1, ∃ reaction ∈ candidate.2,
      source.orientedReactants candidate.1 flow reaction = {entity} := by
  classical
  intro entity hentity
  by_contra hsole
  push Not at hsole
  have hflowNe := pac_flow_ne_zero source candidate hPAC flow hsupport hpositive
  let bad : Finset Reaction := candidate.2.filter (fun reaction =>
    source.orientedProducts candidate.1 flow reaction = {entity})
  let remaining : Finset Reaction := candidate.2 \ bad
  let newFlow : Reaction → ℝ := fun reaction =>
    if reaction ∈ bad then 0 else flow reaction
  have heraseNonempty : (candidate.1.erase entity).Nonempty := by
    rcases hPAC.1.2.1 with ⟨reaction, hreaction⟩
    rcases hPAC.1.2.2.1 reaction hreaction with ⟨hleft, hright⟩
    by_cases hflowPositive : 0 < flow reaction
    · have hleftErase : ∃ other ∈ candidate.1.erase entity,
          0 < source.left reaction other := by
        by_contra hnone
        have hsingleton := positive_filter_eq_singleton_of_erase_none
          candidate.1 entity (source.left reaction) hentity hleft hnone
        exact hsole reaction hreaction (by
          simp [ReversibleSource.orientedReactants, hflowPositive, hsingleton])
      rcases hleftErase with ⟨other, hother, _⟩
      exact ⟨other, hother⟩
    · have hrightErase : ∃ other ∈ candidate.1.erase entity,
          0 < source.right reaction other := by
        by_contra hnone
        have hsingleton := positive_filter_eq_singleton_of_erase_none
          candidate.1 entity (source.right reaction) hentity hright hnone
        exact hsole reaction hreaction (by
          simp [ReversibleSource.orientedReactants, hflowPositive, hsingleton])
      rcases hrightErase with ⟨other, hother, _⟩
      exact ⟨other, hother⟩
  have hremainingSide : ∀ reaction ∈ remaining,
      source.sideAdmissible (candidate.1.erase entity) reaction := by
    intro reaction hreaction
    have hreactionOriginal : reaction ∈ candidate.2 :=
      (Finset.mem_sdiff.mp hreaction).1
    have hnotBad : reaction ∉ bad := (Finset.mem_sdiff.mp hreaction).2
    rcases hPAC.1.2.2.1 reaction hreactionOriginal with ⟨hleft, hright⟩
    constructor
    · by_contra hnone
      have hsingleton := positive_filter_eq_singleton_of_erase_none
        candidate.1 entity (source.left reaction) hentity hleft hnone
      by_cases hflowPositive : 0 < flow reaction
      · exact hsole reaction hreactionOriginal (by
          simp [ReversibleSource.orientedReactants, hflowPositive, hsingleton])
      · apply hnotBad
        exact Finset.mem_filter.mpr ⟨hreactionOriginal, by
          simp [ReversibleSource.orientedProducts, hflowPositive, hsingleton]⟩
    · by_contra hnone
      have hsingleton := positive_filter_eq_singleton_of_erase_none
        candidate.1 entity (source.right reaction) hentity hright hnone
      by_cases hflowPositive : 0 < flow reaction
      · apply hnotBad
        exact Finset.mem_filter.mpr ⟨hreactionOriginal, by
          simp [ReversibleSource.orientedProducts, hflowPositive, hsingleton]⟩
      · exact hsole reaction hreactionOriginal (by
          simp [ReversibleSource.orientedReactants, hflowPositive, hsingleton])
  have hnewSupport : ∀ reaction, reaction ∉ remaining → newFlow reaction = 0 := by
    intro reaction hreaction
    by_cases hreactionBad : reaction ∈ bad
    · simp [newFlow, hreactionBad]
    · simp only [newFlow, hreactionBad, ↓reduceIte]
      apply hsupport reaction
      intro hreactionOriginal
      exact hreaction (Finset.mem_sdiff.mpr ⟨hreactionOriginal, hreactionBad⟩)
  have hnewPositive : ∀ other ∈ candidate.1.erase entity,
      0 < Finset.univ.sum (fun reaction =>
        source.net reaction other * newFlow reaction) := by
    intro other hother
    have holdPositive := hpositive other (Finset.mem_of_mem_erase hother)
    apply lt_of_lt_of_le holdPositive
    apply Finset.sum_le_sum
    intro reaction _hreaction
    by_cases hreactionBad : reaction ∈ bad
    · have hreactionOriginal : reaction ∈ candidate.2 :=
        (Finset.mem_filter.mp hreactionBad).1
      have hproducts : source.orientedProducts candidate.1 flow reaction =
          {entity} := (Finset.mem_filter.mp hreactionBad).2
      have hnonpos := net_mul_nonpos_of_orientedProducts_eq_singleton
        source candidate.1 flow reaction entity other
        (hflowNe reaction hreactionOriginal) hproducts hother
      simpa [newFlow, hreactionBad] using hnonpos
    · simp [newFlow, hreactionBad]
  have hremainingNonempty : remaining.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rcases heraseNonempty with ⟨other, hother⟩
    have hpos := hnewPositive other hother
    have hallZero : ∀ reaction, newFlow reaction = 0 := by
      intro reaction
      apply hnewSupport reaction
      simp [hempty]
    simp [hallZero] at hpos
  let smaller : Candidate Entity Reaction :=
    (candidate.1.erase entity, remaining)
  have hsmallerMotif : source.Motif smaller := by
    exact ⟨heraseNonempty, hremainingNonempty, hremainingSide,
      ⟨newFlow, hnewSupport, hnewPositive⟩⟩
  have hsmaller : smaller < candidate := by
    change smaller ≤ candidate ∧ ¬ candidate ≤ smaller
    constructor
    · exact ⟨Finset.erase_subset entity candidate.1,
        Finset.sdiff_subset.trans (by rfl)⟩
    · intro hback
      have := hback.1 hentity
      change entity ∈ candidate.1.erase entity at this
      exact (Finset.mem_erase.mp this).1 rfl
  exact hPAC.2 hsmaller hsmallerMotif

omit [Fintype Entity] in
theorem pac_card_entities_le_reactions
    (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) (hPAC : source.PAC candidate)
    (flow : Reaction → ℝ)
    (hsupport : ∀ reaction, reaction ∉ candidate.2 → flow reaction = 0)
    (hpositive : ∀ entity ∈ candidate.1,
      0 < Finset.univ.sum (fun reaction =>
        source.net reaction entity * flow reaction)) :
    candidate.1.card ≤ candidate.2.card := by
  classical
  have hsole := pac_entity_is_sole_oriented_reactant
    source candidate hPAC flow hsupport hpositive
  let defaultReaction : Reaction := Classical.choose hPAC.1.2.1
  let owner : Entity → Reaction := fun entity =>
    if hentity : entity ∈ candidate.1 then
      Classical.choose (hsole entity hentity)
    else defaultReaction
  have howner : ∀ entity ∈ candidate.1,
      owner entity ∈ candidate.2 ∧
        source.orientedReactants candidate.1 flow (owner entity) = {entity} := by
    intro entity hentity
    simpa [owner, hentity] using
      (Classical.choose_spec (hsole entity hentity))
  apply Finset.card_le_card_of_injOn owner
  · intro entity hentity
    exact (howner entity hentity).1
  · intro first hfirst second hsecond heq
    have hone := (howner first hfirst).2
    have htwo := (howner second hsecond).2
    rw [heq] at hone
    exact Finset.singleton_inj.mp (hone.symm.trans htwo)

omit [Fintype Entity] in
theorem pac_net_columns_linearIndependent
    (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) (hPAC : source.PAC candidate) :
    LinearIndependent ℝ (fun reaction : ↥candidate.2 =>
      fun entity : ↥candidate.1 => source.net reaction.1 entity.1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro relation hrelation reaction
  by_contra hreactionCoeff
  rcases hPAC.1.2.2.2 with ⟨flow, hsupport, hpositive⟩
  let fullRelation : Reaction → ℝ := Subtype.val.extend relation 0
  have hrelationFull : ∀ entity ∈ candidate.1,
      Finset.univ.sum (fun selected =>
        source.net selected entity * fullRelation selected) = 0 := by
    intro entity hentity
    have hcoordinate := congrFun hrelation ⟨entity, hentity⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoordinate
    change (∑ selected : ↥candidate.2,
      relation selected * source.net selected.1 entity) = 0 at hcoordinate
    have hrestricted : candidate.2.sum (fun selected =>
        source.net selected entity * fullRelation selected) = 0 := by
      rw [← Finset.sum_finset_coe]
      simpa [fullRelation, Subtype.val_injective.extend_apply, mul_comm] using hcoordinate
    calc
      Finset.univ.sum (fun selected =>
          source.net selected entity * fullRelation selected) =
          candidate.2.sum (fun selected =>
            source.net selected entity * fullRelation selected) := by
            symm
            apply Finset.sum_subset (Finset.subset_univ candidate.2)
            intro selected _huniv hnotSelected
            simp [fullRelation, hnotSelected]
      _ = 0 := hrestricted
  let scale : ℝ := -(flow reaction.1) / relation reaction
  let newFlow : Reaction → ℝ := fun selected =>
    flow selected + scale * fullRelation selected
  have hnewAtReaction : newFlow reaction.1 = 0 := by
    simp [newFlow, scale, fullRelation, hreactionCoeff]
  have hnewSupport : ∀ selected,
      selected ∉ candidate.2.erase reaction.1 → newFlow selected = 0 := by
    intro selected hselected
    by_cases heq : selected = reaction.1
    · simpa [heq] using hnewAtReaction
    · have hnotOriginal : selected ∉ candidate.2 := by
        intro horiginal
        exact hselected (Finset.mem_erase.mpr ⟨heq, horiginal⟩)
      have hnotRange : ¬ ∃ x : ↥candidate.2, x.1 = selected := by
        intro hexists
        rcases hexists with ⟨x, hx⟩
        exact hnotOriginal (hx ▸ x.2)
      have hfullZero : fullRelation selected = 0 := by
        simpa using Function.extend_apply' (f := fun x : ↥candidate.2 => x.1)
          relation (0 : Reaction → ℝ) selected hnotRange
      simp [newFlow, hfullZero, hsupport selected hnotOriginal]
  have hnewPositive : ∀ entity ∈ candidate.1,
      0 < Finset.univ.sum (fun selected =>
        source.net selected entity * newFlow selected) := by
    intro entity hentity
    have hzero := hrelationFull entity hentity
    have hscaledZero : Finset.univ.sum (fun selected =>
        source.net selected entity * (scale * fullRelation selected)) = 0 := by
      calc
        Finset.univ.sum (fun selected =>
            source.net selected entity * (scale * fullRelation selected)) =
            Finset.univ.sum (fun selected =>
              scale * (source.net selected entity * fullRelation selected)) := by
                apply Finset.sum_congr rfl
                intro selected _hselected
                ring
        _ = scale * Finset.univ.sum (fun selected =>
              source.net selected entity * fullRelation selected) :=
                (Finset.mul_sum _ _ _).symm
        _ = 0 := by rw [hzero, mul_zero]
    have heq : Finset.univ.sum (fun selected =>
        source.net selected entity * newFlow selected) =
        Finset.univ.sum (fun selected =>
          source.net selected entity * flow selected) := by
      simp only [newFlow, mul_add, Finset.sum_add_distrib]
      rw [hscaledZero, add_zero]
    rw [heq]
    exact hpositive entity hentity
  have herasedNonempty : (candidate.2.erase reaction.1).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rcases hPAC.1.1 with ⟨entity, hentity⟩
    have hpos := hnewPositive entity hentity
    have hallZero : ∀ selected, newFlow selected = 0 := by
      intro selected
      apply hnewSupport selected
      simp [hempty]
    simp [hallZero] at hpos
  let smaller : Candidate Entity Reaction :=
    (candidate.1, candidate.2.erase reaction.1)
  have hsmallerMotif : source.Motif smaller := by
    refine ⟨hPAC.1.1, herasedNonempty, ?_, ⟨newFlow, hnewSupport, hnewPositive⟩⟩
    intro selected hselected
    exact hPAC.1.2.2.1 selected (Finset.mem_of_mem_erase hselected)
  have hsmaller : smaller < candidate := by
    change smaller ≤ candidate ∧ ¬ candidate ≤ smaller
    constructor
    · exact ⟨le_rfl, Finset.erase_subset reaction.1 candidate.2⟩
    · intro hback
      have := hback.2 reaction.2
      change reaction.1 ∈ candidate.2.erase reaction.1 at this
      exact (Finset.mem_erase.mp this).1 rfl
  exact hPAC.2 hsmaller hsmallerMotif

theorem pac_card_reactions_le_entities
    (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) (hPAC : source.PAC candidate) :
    candidate.2.card ≤ candidate.1.card := by
  have hlinear := pac_net_columns_linearIndependent source candidate hPAC
  have hcard := hlinear.fintype_card_le_finrank
  simpa [Module.finrank_fintype_fun_eq_card] using hcard

theorem pac_card_entities_eq_reactions
    (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) (hPAC : source.PAC candidate) :
    candidate.1.card = candidate.2.card := by
  rcases hPAC.1.2.2.2 with ⟨flow, hsupport, hpositive⟩
  exact Nat.le_antisymm
    (pac_card_entities_le_reactions source candidate hPAC flow hsupport hpositive)
    (pac_card_reactions_le_entities source candidate hPAC)

theorem pac_unique_child_selection
    (source : ReversibleSource Entity Reaction)
    (candidate : Candidate Entity Reaction) (hPAC : source.PAC candidate)
    (flow : Reaction → ℝ)
    (hsupport : ∀ reaction, reaction ∉ candidate.2 → flow reaction = 0)
    (hpositive : ∀ entity ∈ candidate.1,
      0 < Finset.univ.sum (fun reaction =>
        source.net reaction entity * flow reaction)) :
    ∃ owner : Entity → Reaction,
      Set.BijOn owner (candidate.1 : Set Entity) (candidate.2 : Set Reaction) ∧
      ∀ entity ∈ candidate.1,
        source.orientedReactants candidate.1 flow (owner entity) = {entity} := by
  classical
  have hsole := pac_entity_is_sole_oriented_reactant
    source candidate hPAC flow hsupport hpositive
  let defaultReaction : Reaction := Classical.choose hPAC.1.2.1
  let owner : Entity → Reaction := fun entity =>
    if hentity : entity ∈ candidate.1 then
      Classical.choose (hsole entity hentity)
    else defaultReaction
  have howner : ∀ entity ∈ candidate.1,
      owner entity ∈ candidate.2 ∧
        source.orientedReactants candidate.1 flow (owner entity) = {entity} := by
    intro entity hentity
    simpa [owner, hentity] using
      (Classical.choose_spec (hsole entity hentity))
  have hmaps : Set.MapsTo owner (candidate.1 : Set Entity)
      (candidate.2 : Set Reaction) := by
    intro entity hentity
    exact (howner entity hentity).1
  have hinj : Set.InjOn owner (candidate.1 : Set Entity) := by
    intro first hfirst second hsecond heq
    have hone := (howner first hfirst).2
    have htwo := (howner second hsecond).2
    rw [heq] at hone
    exact Finset.singleton_inj.mp (hone.symm.trans htwo)
  have himageSubset : candidate.1.image owner ⊆ candidate.2 := by
    intro reaction hreaction
    rcases Finset.mem_image.mp hreaction with ⟨entity, hentity, rfl⟩
    exact hmaps hentity
  have himageCard : (candidate.1.image owner).card = candidate.1.card :=
    Finset.card_image_of_injOn hinj
  have hcardEq : candidate.1.card = candidate.2.card :=
    Nat.le_antisymm
      (pac_card_entities_le_reactions source candidate hPAC flow hsupport hpositive)
      (pac_card_reactions_le_entities source candidate hPAC)
  have himageEq : candidate.1.image owner = candidate.2 := by
    apply Finset.eq_of_subset_of_card_le himageSubset
    rw [himageCard, hcardEq]
  have hsurj : Set.SurjOn owner (candidate.1 : Set Entity)
      (candidate.2 : Set Reaction) := by
    intro reaction hreaction
    have hmem : reaction ∈ candidate.1.image owner := by
      rw [himageEq]
      exact hreaction
    rcases Finset.mem_image.mp hmem with ⟨entity, hentity, heq⟩
    exact ⟨entity, hentity, heq⟩
  exact ⟨owner, ⟨hmaps, hinj, hsurj⟩, fun entity hentity =>
    (howner entity hentity).2⟩

end UnconstrainedPACDetection

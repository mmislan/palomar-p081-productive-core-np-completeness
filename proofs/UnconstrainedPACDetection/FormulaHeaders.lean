module

public import proofs.UnconstrainedPACDetection.FormulaReactionFinish

@[expose] public section

namespace UnconstrainedPACDetection.FormulaHeaders
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def clauses (src : List Bool) : Nat := FormulaTokenCount.run true none src
def value (src : List Bool) : Nat := FormulaReactionRegisters.value (clauses src)
  (FormulaHeaderPreparation.occurrences src) (FormulaHeaderPreparation.maximum src+1)
def fields (src : List Bool) : List Bool :=
  BinaryFields.encodeField (FormulaEntityHeader.value src).bits ++
  BinaryFields.encodeField (value src).bits

def finished (src : List Bool) : Complexity.TM.TapePred 7 := fun i w o =>
  i = word src ∧ w 0 = regTape (clauses src) ∧
  w 1 = regTape (FormulaHeaderPreparation.occurrences src) ∧
  w 2 = regTape (FormulaHeaderPreparation.maximum src+1) ∧
  w 3 = word [true] ∧ w 4 = regTape (FormulaEntityHeader.value src) ∧
  w 5 = regTape (value src) ∧ w 6 = word (value src).bits ∧ OutAcc (fields src) o

theorem entity_parked (src : List Bool) {i w o}
    (h : FormulaEntityHeader.finished src i w o) : ∀ j, Parked (w j) := by
  obtain ⟨_,⟨h0,h1,h2,h3,h4⟩,h5,h6,_⟩ := h
  intro j
  fin_cases j
  · change Parked (w 0); rw [h0]; exact word_parked _
  · change Parked (w 1); rw [h1]; exact parked_regTape _
  · change Parked (w 2); rw [h2]; exact parked_regTape _
  · exact h3.parked
  · change Parked (w 4); rw [h4]; exact parked_regTape _
  · change Parked (w 5); rw [h5]; exact word_parked _
  · change Parked (w 6); rw [h6]; exact word_parked _

theorem parameter_bounds (src : List Bool) :
    clauses src ≤ src.length+1 ∧ FormulaHeaderPreparation.occurrences src ≤ src.length+1 ∧
    FormulaHeaderPreparation.maximum src+1 ≤ 3*src.length+2 := by
  have hc := FormulaTokenCount.run_bound true none src
  have ho := FormulaHeaderPreparation.occurrences_bound src
  have hm := FormulaMaximumRestore.value_bound src
  exact ⟨by simpa [clauses] using hc.trans (Nat.le_succ _),ho,by
    simpa [FormulaHeaderPreparation.maximum] using Nat.add_le_add_right hm 1⟩

def finishBound (src : List Bool) : Nat :=
  40*(opBudget (FormulaHeaderPreparation.cap src)+1)+9*src.length+
    2*(FormulaHeaderPreparation.cap src+1)+24*(FormulaHeaderPreparation.cap src+1)^2+40

theorem finish_hoare (src : List Bool) : FormulaReactionFinish.machine.HoareTime
    (FormulaEntityHeader.finished src) (finished src) (finishBound src) := by
  intro i w o h
  have hp := entity_parked src h
  obtain ⟨hin,⟨h0,h1,h2,h3,h4⟩,h5,h6,hout⟩ := h
  subst i
  obtain ⟨hc,ho,hv⟩ := parameter_bounds src
  have hr := FormulaReactionRegisters.value_bound src.length _ _ _ hc ho hv
  have he := FormulaHeaderRegisters.value_bound src.length _ _ ho hv
  have hcall := FormulaReactionFinish.finish_hoare (clauses src)
    (FormulaHeaderPreparation.occurrences src) (FormulaHeaderPreparation.maximum src+1)
    (FormulaHeaderPreparation.cap src) (FormulaMaximum.maximumBits src)
    (FormulaEntityHeader.value src).bits
    (BinaryFields.encodeField (FormulaEntityHeader.value src).bits) (word src) w
    (word_parked src) hp
    (by simpa [clauses,FormulaTokenCount.countBits,FormulaEndpointRegisters.unary_word] using h0)
    h1 h2 h3 (by simpa only [← FormulaEndpointRegisters.unary_word 1,List.replicate_one] using h5) h6
    (by unfold FormulaHeaderPreparation.cap; nlinarith)
    (by unfold FormulaHeaderPreparation.cap; nlinarith)
    (by unfold FormulaHeaderPreparation.cap; nlinarith) hr
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := hcall (word src) w o ⟨rfl,rfl,hout⟩
  refine ⟨d,t,?_,hd,hh,hdi,?_,?_,?_,?_,?_,?_,?_,hdo⟩
  · have hm := FormulaMaximumRestore.value_bound src
    have hl := VerifierUnaryBinary.digits_length (FormulaEntityHeader.value src)
    rw [FormulaHeaderBinaryDigits.digits_eq_bits] at hl
    have hx : (FormulaMaximum.maximumBits src).length ≤ 3*src.length+1 := by
      simpa [FormulaMaximum.maximumBits,FormulaMaximumFrame.value] using hm
    have hr' : value src ≤ FormulaHeaderPreparation.cap src := hr
    have he' : FormulaEntityHeader.value src ≤ FormulaHeaderPreparation.cap src := he
    have hs : (value src+1)^2 ≤ (FormulaHeaderPreparation.cap src+1)^2 := by nlinarith
    change t ≤ finishBound src
    change t ≤ 40*(opBudget (FormulaHeaderPreparation.cap src)+1)+
      3*(FormulaMaximum.maximumBits src).length+2*(FormulaEntityHeader.value src).bits.length+
      24*(value src+1)^2+30 at ht
    unfold finishBound
    omega
  all_goals rw [hdw]
  · simpa [FormulaReactionFinish.finalBank,FormulaReactionFinish.cleanBank,
      FormulaReactionField.afterWork,FormulaReactionRegisters.bank,clauses,
      FormulaTokenCount.countBits,FormulaEndpointRegisters.unary_word] using h0
  · simpa [FormulaReactionFinish.finalBank,FormulaReactionFinish.cleanBank,
      FormulaReactionField.afterWork,FormulaReactionRegisters.bank] using h1
  · simpa [FormulaReactionFinish.finalBank,FormulaReactionFinish.cleanBank,
      FormulaReactionField.afterWork,FormulaReactionRegisters.bank] using h2
  · simp [FormulaReactionFinish.finalBank,FormulaReactionFinish.cleanBank,
      FormulaReactionField.afterWork,FormulaReactionRegisters.bank]
  · simpa [FormulaReactionFinish.finalBank,FormulaReactionFinish.cleanBank,
      FormulaReactionField.afterWork,FormulaReactionRegisters.bank] using h4
  · simp [FormulaReactionFinish.finalBank,FormulaReactionFinish.cleanBank,
      FormulaReactionField.afterWork,FormulaReactionRegisters.bank,value]
  · simp [FormulaReactionFinish.finalBank,FormulaReactionFinish.cleanBank,
      FormulaReactionField.afterWork,FormulaReactionRegisters.bank,value]

@[reducible] def machine : TM 7 := seqTM FormulaEntityHeader.machine FormulaReactionFinish.machine
def bound (src : List Bool) : Nat := FormulaEntityHeader.bound src+1+finishBound src

theorem ordinary_hoare (src : List Bool) : machine.HoareTime
    (FormulaEntityHeader.initial src) (finished src) (bound src) := by
  have hs : ∀ i w o, FormulaEntityHeader.finished src i w o →
      FormulaEntityHeader.finished src (transitionInput i)
        (fun j => transitionTape (w j)) (transitionTape o) := by
    intro i w o h
    obtain ⟨hi,hw,ho⟩ := phaseTransition_eq_self_of_reads_ne_start
      (h.1 ▸ (word_parked src).read_ne_start)
      (fun j => (entity_parked src h j).read_ne_start) h.2.2.2.2.parked.read_ne_start
    simpa only [hi,hw,ho] using h
  exact seqTM_hoareTime _ _ (FormulaEntityHeader.ordinary_hoare src) hs (finish_hoare src)

theorem decoded_values (φ : SAT.CNF) :
    FormulaEntityHeader.value φ.encode = (FormulaPACEncoding.table φ).entities ∧
    value φ.encode = (FormulaPACEncoding.table φ).reactions := by
  obtain ⟨_,ho⟩ := FormulaTokenCount.decoded_output φ.encode φ (SAT.CNF.decode?_encode φ)
  have hc := congrArg List.length ho
  simp only [FormulaTokenCount.countBits,List.length_replicate] at hc
  have hm := FormulaMaximum.decoded_maximum φ.encode φ (SAT.CNF.decode?_encode φ)
  have hcl : clauses φ.encode = φ.length := by
    simp [clauses,FormulaTokenCount.formula_count]
  constructor
  · simpa only [FormulaEntityHeader.value,FormulaHeaderPreparation.maximum,
      FormulaHeaderPreparation.occurrences,FormulaMaximumFrame.value,FormulaWiring.varCount,hm,hc]
      using FormulaHeaderRegisters.formula_value φ
  · simpa only [value,hcl,FormulaHeaderPreparation.maximum,
      FormulaHeaderPreparation.occurrences,FormulaMaximumFrame.value,FormulaWiring.varCount,hm,hc]
      using FormulaReactionRegisters.formula_value φ

/-- Both canonical dimension fields, produced from ordinary formula input. -/
theorem decoded_headers (φ : SAT.CNF) :
    machine.HoareTime (FormulaEntityHeader.initial φ.encode)
      (fun i _w o => i = word φ.encode ∧ OutAcc
        (BinaryFields.encodeField (FormulaPACEncoding.table φ).entities.bits ++
         BinaryFields.encodeField (FormulaPACEncoding.table φ).reactions.bits) o)
      (bound φ.encode) := by
  obtain ⟨he,hr⟩ := decoded_values φ
  apply (ordinary_hoare φ.encode).consequence
  · intro i w o h; exact h
  · rintro i w o ⟨hi,_,_,_,_,_,_,_,ho⟩
    exact ⟨hi,by simpa only [fields,he,hr] using ho⟩
  · omega

end UnconstrainedPACDetection.FormulaHeaders

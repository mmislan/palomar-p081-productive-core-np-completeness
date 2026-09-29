module

public import proofs.UnconstrainedPACDetection.FormulaHeaderRegisters
public import proofs.UnconstrainedPACDetection.FormulaEndpointRegisters

@[expose] public section

namespace UnconstrainedPACDetection.FormulaHeaderPreparation
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def occurrences (src : List Bool) : Nat := FormulaTokenCount.run false none src
def maximum (src : List Bool) : Nat := FormulaMaximumFrame.value src
def cap (src : List Bool) : Nat := 128*(src.length+1)^2

def frame (src : List Bool) (v d : Nat) : Complexity.TM.TapePred 5 := fun inp work out =>
  inp = word src ∧ work 0 = word (FormulaTokenCount.countBits true src) ∧
    work 1 = regTape (occurrences src) ∧ work 2 = regTape v ∧
    OutAcc (FormulaMaximum.maximumBits src) (work 3) ∧ work 4 = regTape d ∧ OutAcc [] out

theorem parked (src : List Bool) (v d : Nat) {inp : Tape} {work : Fin 5 → Tape} {out : Tape}
    (h : frame src v d inp work out) : ∀ i, Parked (work i) := by
  obtain ⟨_,h0,h1,h2,h3,h4,_⟩ := h
  intro i
  fin_cases i
  · change Parked (work 0); rw [h0]; exact word_parked _
  · change Parked (work 1); rw [h1]; exact parked_regTape _
  · change Parked (work 2); rw [h2]; exact parked_regTape _
  · exact h3.parked
  · change Parked (work 4); rw [h4]; exact parked_regTape _

theorem stable (src : List Bool) (v d : Nat) : ∀ inp work out,
    frame src v d inp work out → frame src v d (transitionInput inp)
      (fun i => transitionTape (work i)) (transitionTape out) := by
  intro inp work out h
  have hp := parked src v d h
  have hi := h.1
  have ho := h.2.2.2.2.2.2
  obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start
    (hi ▸ (word_parked src).read_ne_start) (fun j => (hp j).read_ne_start) ho.parked.read_ne_start
  simpa only [hin,hw,hout] using h

def emptyBank : Fin 5 → Tape := fun _ => regTape 0
def placed : TM 5 := placeWorkTM 0 1 FormulaParameters.prepared

theorem placed_hoare (src : List Bool) : placed.HoareTime
    (EmitPred (word src) emptyBank []) (frame src (maximum src) 0) (15*src.length+35) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hr,hh,hi,h0,h1,h2,h3,hout⟩ := FormulaParameters.prepared_hoare src []
    _ _ out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    FormulaParameters.prepared 0 1 emptyBank hr
    (by intro j _; exact (parked_regTape 0).read_ne_start)
  refine ⟨placeWorkCfg _ 0 1 emptyBank d,t,ht,?_,hh,hi,h0,?_,h2,h3,rfl,hout⟩
  · unfold placed
    convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;>
        simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,emptyBank,
          FormulaParameters.bank,FormulaParameters.empty_reg]
    · rfl
  · simpa [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,occurrences,
      FormulaTokenCount.countBits,FormulaEndpointRegisters.unary_word] using h1

def initial (src : List Bool) : Complexity.TM.TapePred 5 := fun inp work out =>
  inp = Tape.init (src.map Γ.ofBool) ∧ (∀ j, work j = Tape.init []) ∧ out = Tape.init []

theorem bump_hoare (src : List Bool) : (bumpTM (n := 5)).HoareTime
    (initial src) (EmitPred (word src) emptyBank []) 1 := by
  apply (bumpTM_hoareTime src).consequence
  · intro inp work out h; exact h
  · rintro inp work out ⟨hi,hw,ho⟩
    exact ⟨hi,funext (fun j => (hw j).eq_regT),ho⟩
  · omega

def counts : TM 5 := seqTM bumpTM placed

theorem counts_hoare (src : List Bool) : counts.HoareTime
    (initial src) (frame src (maximum src) 0) (15*src.length+37) := by
  have h := seqTM_hoareTime _ _ (bump_hoare src)
    (emitPred_transition (word_parked src) (fun _ => parked_regTape 0) []) (placed_hoare src)
  exact h.mono_bound (by omega)

theorem increment_hoare (src : List Bool) (v : Nat) : (incRegTM (2 : Fin 5)).HoareTime
    (frame src v 0) (frame src (v+1) 0) (2*v+4) := by
  intro inp work out h
  have hp := parked src v 0 h
  obtain ⟨rfl,h0,h1,h2,h3,h4,ho⟩ := h
  obtain ⟨d,t,ht,hr,hh,hi,hw,hout⟩ := incRegTM_hoareTime (2 : Fin 5) v (word src) work []
    (word_parked src) (fun j _ => hp j) h2 _ _ out ⟨rfl,rfl,ho⟩
  refine ⟨d,t,ht,hr,hh,hi,?_,?_,?_,?_,?_,hout⟩
  all_goals rw [hw]
  · simpa using h0
  · simpa using h1
  · simp
  · simpa using h3
  · simpa using h4

theorem occurrences_bound (src : List Bool) : occurrences src ≤ src.length+1 := by
  have h := FormulaCountRegisters.count_length false src
  simpa [occurrences,FormulaTokenCount.countBits] using h

theorem arithmetic_hoare (src : List Bool) (v : Nat) (hv : v ≤ 3*src.length+2) :
    FormulaHeaderRegisters.machine.HoareTime (frame src v 0)
      (frame src v (FormulaHeaderRegisters.value (occurrences src) v))
      (50*(opBudget (cap src)+1)) := by
  intro inp work out h
  have hp := parked src v 0 h
  obtain ⟨rfl,h0,h1,h2,h3,h4,ho⟩ := h
  have ha := occurrences_bound src
  have he := FormulaHeaderRegisters.value_bound src.length (occurrences src) v ha hv
  have ham : occurrences src ≤ cap src := by unfold cap; nlinarith
  have hbm : v ≤ cap src := by unfold cap; nlinarith
  obtain ⟨d,t,ht,hr,hh,hi,hw,hout⟩ := FormulaHeaderRegisters.arithmetic_hoare
    (occurrences src) v (cap src) (word src) work [] (word_parked src) hp h1 h2 h4
    ham hbm he _ _ out ⟨rfl,rfl,ho⟩
  refine ⟨d,t,ht,hr,hh,hi,?_,?_,?_,?_,?_,hout⟩
  all_goals rw [hw]; dsimp [FormulaHeaderRegisters.bank]
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · rfl

def finish : TM 5 := seqTM (incRegTM 2) FormulaHeaderRegisters.machine
def machine : TM 5 := seqTM counts finish
def timeBound (src : List Bool) : Nat := 50*(opBudget (cap src)+1)+21*src.length+45

/-- Original raw bits to a live entity-count register, with every preparation step charged. -/
theorem ordinary_hoare (src : List Bool) : machine.HoareTime (initial src)
    (frame src (maximum src+1) (FormulaHeaderRegisters.value (occurrences src) (maximum src+1)))
    (timeBound src) := by
  have hm := FormulaMaximumRestore.value_bound src
  have hv : maximum src+1 ≤ 3*src.length+2 := by simpa [maximum] using Nat.add_le_add_right hm 1
  have hf := seqTM_hoareTime _ _ (increment_hoare src (maximum src))
    (stable src (maximum src+1) 0) (arithmetic_hoare src (maximum src+1) hv)
  have h := seqTM_hoareTime _ _ (counts_hoare src) (stable src (maximum src) 0) hf
  apply h.mono_bound
  unfold timeBound maximum
  omega

theorem decoded_hoare (φ : SAT.CNF) : machine.HoareTime (initial φ.encode)
    (frame φ.encode (FormulaWiring.varCount φ) (FormulaPACEncoding.table φ).entities)
    (timeBound φ.encode) := by
  have h := ordinary_hoare φ.encode
  obtain ⟨_,ho⟩ := FormulaTokenCount.decoded_output φ.encode φ (SAT.CNF.decode?_encode φ)
  have hc := congrArg List.length ho
  simp only [FormulaTokenCount.countBits,List.length_replicate] at hc
  have hm := FormulaMaximum.decoded_maximum φ.encode φ (SAT.CNF.decode?_encode φ)
  simpa only [maximum,occurrences,FormulaMaximumFrame.value,hm,hc,
    FormulaWiring.varCount,← FormulaHeaderRegisters.formula_value] using h

end UnconstrainedPACDetection.FormulaHeaderPreparation

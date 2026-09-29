module

public import proofs.UnconstrainedPACDetection.FormulaCountPair
public import proofs.UnconstrainedPACDetection.FormulaMaximumRestore
public import proofs.UnconstrainedPACDetection.VerifierOutputRouting

@[expose] public section

namespace UnconstrainedPACDetection.FormulaParameters
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def bank (xs ys : List Bool) : Fin 4 → Tape := ![word xs,word ys,regTape 0,word []]

theorem bank_parked (xs ys : List Bool) : ∀ j, Parked (bank xs ys j) := by
  intro j
  fin_cases j
  all_goals first | exact word_parked _ | exact parked_regTape _

def counts : TM 4 := placeWorkTM 0 2 FormulaCountPair.machine

theorem counts_hoare (src emitted : List Bool) : counts.HoareTime
    (EmitPred (word src) (bank [] []) emitted)
    (EmitPred (word src)
      (bank (FormulaTokenCount.countBits true src) (FormulaTokenCount.countBits false src)) emitted)
    (6*src.length+23) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hr,hh,hi,hw,hout⟩ := FormulaCountPair.ready_hoare src emitted
    _ _ out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal FormulaCountPair.machine
    0 2 (bank [] []) hr (by intro j _; exact (bank_parked [] [] j).read_ne_start)
  refine ⟨placeWorkCfg _ 0 2 (bank [] []) d,t,ht,?_,hh,hi,?_,hout⟩
  · unfold counts
    convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,bank,hw,FormulaCountPair.bank]
    all_goals rfl

def maxResult (src emitted : List Bool) : Complexity.TM.TapePred 2 := fun inp work out =>
  inp = word src ∧ work 0 = regTape (FormulaMaximumFrame.value src) ∧
    OutAcc (FormulaMaximum.maximumBits src) (work 1) ∧ OutAcc emitted out

theorem maximum_hoare (src emitted : List Bool) :
    FormulaMaximumRestore.machine.retargetOutput.HoareTime
      (EmitPred (word src) ![regTape 0,word []] emitted) (maxResult src emitted)
      (9*src.length+11) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hr,hh,hi,hw,hout⟩ := FormulaMaximumRestore.ready_hoare src
    _ _ _ ⟨rfl,rfl,outAcc_nil_init⟩
  have hs := VerifierOutputRouting.run_frame _ out ho.parked.read_ne_start hr
  refine ⟨VerifierOutputRouting.wrap _ out d,t,ht,?_,hh,hi,?_,hout,ho⟩
  · unfold retargetOutput at hs ⊢
    convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j
      fin_cases j <;>
        simp [VerifierOutputRouting.wrap,retargetCfg,word,List.map_nil,Tape.move]
    · rfl
  · change d.work 0 = _
    rw [hw]

def ready (src emitted : List Bool) : Complexity.TM.TapePred 4 := fun inp work out =>
  inp = word src ∧ work 0 = word (FormulaTokenCount.countBits true src) ∧
    work 1 = word (FormulaTokenCount.countBits false src) ∧
    work 2 = regTape (FormulaMaximumFrame.value src) ∧
    OutAcc (FormulaMaximum.maximumBits src) (work 3) ∧ OutAcc emitted out

def maximum : TM 4 := placeWorkTM 2 0 FormulaMaximumRestore.machine.retargetOutput

theorem placed_maximum_hoare (src emitted : List Bool) : maximum.HoareTime
    (EmitPred (word src)
      (bank (FormulaTokenCount.countBits true src) (FormulaTokenCount.countBits false src)) emitted)
    (ready src emitted) (9*src.length+11) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hr,hh,hi,hm,hscratch,hout⟩ := maximum_hoare src emitted
    _ _ out ⟨rfl,rfl,ho⟩
  let base := bank (FormulaTokenCount.countBits true src) (FormulaTokenCount.countBits false src)
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    FormulaMaximumRestore.machine.retargetOutput 2 0 base hr
    (by intro j _; exact (bank_parked _ _ j).read_ne_start)
  refine ⟨placeWorkCfg _ 2 0 base d,t,ht,?_,hh,hi,rfl,rfl,hm,hscratch,hout⟩
  unfold maximum
  convert hs using 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j; fin_cases j <;> rfl
  · rfl

theorem bank_stable (src xs ys emitted : List Bool) : ∀ inp work out,
    EmitPred (word src) (bank xs ys) emitted inp work out →
    EmitPred (word src) (bank xs ys) emitted (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨hi,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start
    (word_parked src).read_ne_start (fun j => (bank_parked xs ys j).read_ne_start) ho.parked.read_ne_start
  exact ⟨hi,hw,by rw [hout]; exact ho⟩

def prepared : TM 4 := seqTM counts maximum

theorem prepared_hoare (src emitted : List Bool) : prepared.HoareTime
    (EmitPred (word src) (bank [] []) emitted) (ready src emitted) (15*src.length+35) := by
  have h := seqTM_hoareTime _ _ (counts_hoare src emitted)
    (bank_stable src _ _ emitted) (placed_maximum_hoare src emitted)
  exact h.mono_bound (by omega)

def initial (src : List Bool) : Complexity.TM.TapePred 4 := fun inp work out =>
  inp = Tape.init (src.map Γ.ofBool) ∧ (∀ j, work j = Tape.init []) ∧ out = Tape.init []

theorem empty_reg : word [] = regTape 0 := reg_zero_init_bumped.eq_regT

theorem bump_hoare (src : List Bool) : (bumpTM (n := 4)).HoareTime
    (initial src) (EmitPred (word src) (bank [] []) []) 1 := by
  apply (bumpTM_hoareTime src).consequence
  · intro inp work out h; exact h
  · rintro inp work out ⟨hi,hw,ho⟩
    refine ⟨hi,?_,ho⟩
    funext j
    have he := (hw j).eq_regT
    fin_cases j <;> simpa [bank,empty_reg] using he
  · omega

def machine : TM 4 := seqTM bumpTM prepared

/-- All raw input bits reach exact parameter tapes, with the input restored. -/
theorem ordinary_hoare (src : List Bool) : machine.HoareTime
    (initial src) (ready src []) (15*src.length+37) := by
  have h := seqTM_hoareTime _ _ (bump_hoare src) (bank_stable src [] [] [])
    (prepared_hoare src [])
  exact h.mono_bound (by omega)

/-- Valid formulas receive their semantic counts and maximum in the same raw-input run. -/
theorem decoded_hoare (φ : SAT.CNF) : machine.HoareTime (initial φ.encode)
    (fun inp work out => inp = word φ.encode ∧
      work 0 = word (List.replicate φ.length true) ∧
      work 1 = word (List.replicate (FormulaWiring.occurrences φ).length true) ∧
      work 2 = regTape φ.maxVar ∧ OutAcc (List.replicate φ.maxVar true) (work 3) ∧ OutAcc [] out)
    (15*φ.encode.length+37) := by
  obtain ⟨hc,ho⟩ := FormulaTokenCount.decoded_output φ.encode φ (SAT.CNF.decode?_encode φ)
  have hm := FormulaMaximum.decoded_maximum φ.encode φ (SAT.CNF.decode?_encode φ)
  apply (ordinary_hoare φ.encode).consequence
  · intro inp work out h; exact h
  · rintro inp work out ⟨hi,hc',ho',hm',hs,he⟩
    refine ⟨hi,?_,?_,?_,?_,he⟩
    · simpa only [hc] using hc'
    · simpa only [ho] using ho'
    · simpa only [FormulaMaximumFrame.value,hm] using hm'
    · simpa only [FormulaMaximum.maximumBits,hm] using hs
  · omega

end UnconstrainedPACDetection.FormulaParameters

module

public import proofs.UnconstrainedPACDetection.FormulaCountRegisters

@[expose] public section

namespace UnconstrainedPACDetection.FormulaCountPair
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def bank (xs ys : List Bool) : Fin 2 → Tape := ![word xs,word ys]

theorem bank_parked (xs ys : List Bool) : ∀ j, Parked (bank xs ys j) := by
  intro j; fin_cases j <;> exact word_parked _

def left : TM 2 := placeWorkTM 0 1 (FormulaCountRegisters.machine true)
def right : TM 2 := placeWorkTM 1 0 (FormulaCountRegisters.machine false)

theorem left_hoare (src ys emitted : List Bool) : left.HoareTime
    (EmitPred (word src) (bank [] ys) emitted)
    (EmitPred (word src) (bank (FormulaTokenCount.countBits true src) ys) emitted)
    (3*src.length+11) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hr,hh,hi,hw,hout⟩ := FormulaCountRegisters.ready_hoare true src emitted
    _ _ out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    (FormulaCountRegisters.machine true) 0 1 (bank [] ys) hr
    (by intro j _; exact (bank_parked [] ys j).read_ne_start)
  refine ⟨placeWorkCfg _ 0 1 (bank [] ys) d,t,ht,?_,hh,hi,?_,hout⟩
  · unfold left
    convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,bank,hw]

theorem right_hoare (src xs emitted : List Bool) : right.HoareTime
    (EmitPred (word src) (bank xs []) emitted)
    (EmitPred (word src) (bank xs (FormulaTokenCount.countBits false src)) emitted)
    (3*src.length+11) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hr,hh,hi,hw,hout⟩ := FormulaCountRegisters.ready_hoare false src emitted
    _ _ out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    (FormulaCountRegisters.machine false) 1 0 (bank xs []) hr
    (by intro j _; exact (bank_parked xs [] j).read_ne_start)
  refine ⟨placeWorkCfg _ 1 0 (bank xs []) d,t,ht,?_,hh,hi,?_,hout⟩
  · unfold right
    convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,bank,hw]

theorem stable (src xs ys emitted : List Bool) : ∀ inp work out,
    EmitPred (word src) (bank xs ys) emitted inp work out →
    EmitPred (word src) (bank xs ys) emitted (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨hi,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start
    (word_parked src).read_ne_start (fun j => (bank_parked xs ys j).read_ne_start)
    ho.parked.read_ne_start
  exact ⟨hi,hw,by rw [hout]; exact ho⟩

def machine : TM 2 := seqTM left right

/-- Two consecutive source scans populate separate reusable count tapes. -/
theorem ready_hoare (src emitted : List Bool) : machine.HoareTime
    (EmitPred (word src) (bank [] []) emitted)
    (EmitPred (word src)
      (bank (FormulaTokenCount.countBits true src) (FormulaTokenCount.countBits false src)) emitted)
    (6*src.length+23) := by
  have h := seqTM_hoareTime _ _ (left_hoare src [] emitted)
    (stable src _ [] emitted) (right_hoare src _ emitted)
  exact h.mono_bound (by omega)

theorem decoded_hoare (φ : SAT.CNF) (emitted : List Bool) : machine.HoareTime
    (EmitPred (word φ.encode) (bank [] []) emitted)
    (EmitPred (word φ.encode)
      (bank (List.replicate φ.length true)
        (List.replicate (FormulaWiring.occurrences φ).length true)) emitted)
    (6*φ.encode.length+23) := by
  obtain ⟨hc,ho⟩ := FormulaTokenCount.decoded_output φ.encode φ (SAT.CNF.decode?_encode φ)
  simpa only [hc,ho] using ready_hoare φ.encode emitted

end UnconstrainedPACDetection.FormulaCountPair

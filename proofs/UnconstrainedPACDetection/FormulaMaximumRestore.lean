module

public import proofs.UnconstrainedPACDetection.FormulaMaximumFrame

@[expose] public section

namespace UnconstrainedPACDetection.FormulaMaximumRestore
open Complexity Complexity.TM
open FormulaMaximumFrame (value)
open FormulaMaximum (cursor maximumBits)
open VerifierPairRestore (word word_parked)

def middle (src : List Bool) : Complexity.TM.TapePred 1 := fun inp work out =>
  inp = word src ∧ OutAcc (maximumBits src) out ∧
    ∃ j ≤ value src, work = fun _ => cursor (value src) j

theorem input_hoare (src : List Bool) : (rewindInputTM (n := 1)).HoareTime
    (FormulaMaximumFrame.result src) (middle src) (3*src.length+4) := by
  let P : Complexity.TM.TapePred 1 := fun inp work out =>
    inp.cells = (word src).cells ∧ OutAcc (maximumBits src) out ∧
      ∃ j ≤ value src, work = fun _ => cursor (value src) j
  have h := rewindInputTM_hoareTime_frame (3*src.length+2) (P := P) (by
    rintro inp work out inp' work' out' ⟨hc,ho,hw⟩ he _ rfl rfl
    exact ⟨he.trans hc,ho,hw⟩)
  apply h.consequence
  · intro inp work out hr
    have hp := FormulaMaximumFrame.result_parked src hr
    obtain ⟨hc,hi,hb,ho,hw⟩ := hr
    exact ⟨hi.1,hi.2,hb,ho.parked.read_ne_start,ho.parked.1,
      (fun j => ⟨(hp j).read_ne_start,(hp j).1⟩),hc,ho,hw⟩
  · rintro inp work out ⟨hh,hc,ho,hw⟩
    exact ⟨Tape.ext hh hc,ho,hw⟩
  · omega

theorem work_hoare (src : List Bool) : (rewindWorkTM (0 : Fin 1)).HoareTime
    (middle src) (EmitPred (word src) (fun _ => regTape (value src)) (maximumBits src))
    (value src+3) := by
  let P : Complexity.TM.TapePred 1 := fun inp work out =>
    inp = word src ∧ (work 0).cells = regCells (value src) ∧ OutAcc (maximumBits src) out
  have h := rewindWorkTM_hoareTime_frame (0 : Fin 1) (value src+1) (P := P) (by
    rintro inp work out inp' work' out' ⟨hi,hc,ho⟩ he _ _ rfl hoc hoh
    exact ⟨hi,he.trans hc,(Tape.ext hoh hoc).symm ▸ ho⟩)
  apply h.consequence
  · rintro inp work out ⟨rfl,ho,k,hk,rfl⟩
    refine ⟨regCells_zero (value src),?_,?_,(word_parked src).read_ne_start,
      ho.parked.read_ne_start,ho.parked.1,?_,rfl,rfl,ho⟩
    · exact fun i hi => regCells_ne_start hi
    · change k+1 ≤ value src+1; omega
    · intro j hj
      fin_cases j
      exact False.elim (hj rfl)
  · rintro inp work out ⟨hh,hi,hc,ho⟩
    refine ⟨hi,?_,ho⟩
    funext j
    fin_cases j
    exact Tape.ext hh hc
  · omega

theorem middle_stable (src : List Bool) : ∀ inp work out,
    middle src inp work out → middle src (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have hold := h
  obtain ⟨hi,ho,k,_,hw⟩ := h
  have hp : ∀ j, Parked (work j) := by
    intro j
    rw [hw]
    exact ⟨by simp [cursor],fun i hi => regCells_ne_start hi⟩
  obtain ⟨hin,hwork,hout⟩ := phaseTransition_eq_self_of_reads_ne_start
    (hi ▸ (word_parked src).read_ne_start) (fun j => (hp j).read_ne_start) ho.parked.read_ne_start
  simpa only [hin,hwork,hout] using hold

theorem value_bound (src : List Bool) : value src ≤ 3*src.length+1 := by
  obtain ⟨d,t,ht,hr,_,_,_,_,ho,_⟩ := FormulaMaximumFrame.scan_hoare src
    _ _ _ ⟨rfl,rfl,outAcc_nil_init⟩
  have hb := (head_le_start_add_of_reachesIn _ hr).2.1
  change d.output.head ≤ 1+t at hb
  rw [ho.1] at hb
  simp only [maximumBits,List.length_replicate] at hb
  unfold value
  omega

def restore : TM 1 := seqTM rewindInputTM (rewindWorkTM 0)

theorem restore_hoare (src : List Bool) : restore.HoareTime
    (FormulaMaximumFrame.result src)
    (EmitPred (word src) (fun _ => regTape (value src)) (maximumBits src))
    (6*src.length+9) := by
  have h := seqTM_hoareTime _ _ (input_hoare src) (middle_stable src) (work_hoare src)
  apply h.mono_bound
  have hb := value_bound src
  omega

def machine : TM 1 := seqTM FormulaMaximum.machine restore

/-- Actual maximum scan and both rewinds, exposing the reusable maximum register. -/
theorem ready_hoare (src : List Bool) : machine.HoareTime
    (EmitPred (word src) (fun _ => regTape 0) [])
    (EmitPred (word src) (fun _ => regTape (value src)) (maximumBits src))
    (9*src.length+11) := by
  have h := seqTM_hoareTime _ _ (FormulaMaximumFrame.scan_hoare src)
    (FormulaMaximumFrame.result_stable src) (restore_hoare src)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.FormulaMaximumRestore

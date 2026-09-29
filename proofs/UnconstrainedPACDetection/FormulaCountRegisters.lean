module

public import proofs.UnconstrainedPACDetection.FormulaTokenCountMachine
public import proofs.UnconstrainedPACDetection.FormulaLookupFrame
public import proofs.UnconstrainedPACDetection.VerifierOutputRouting

@[expose] public section

namespace UnconstrainedPACDetection.FormulaCountRegisters
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def scanned (sep : Bool) (src : List Bool) : Complexity.TM.TapePred 0 := fun inp _ out =>
  inp.cells = (word src).cells ∧ inp.StartInvariant ∧ inp.head ≤ src.length+2 ∧
    OutAcc (FormulaTokenCount.countBits sep src) out

theorem scan_hoare (sep : Bool) (src : List Bool) :
    (FormulaTokenCount.machine sep).HoareTime
      (EmitPred (word src) (fun j => nomatch j) []) (scanned sep src) (src.length+1) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  have he : out = word [] := ho.eq outAcc_nil_init
  subst out
  let c : Cfg 0 (FormulaTokenCount.machine sep).Q :=
    ⟨(FormulaTokenCount.machine sep).qstart,word src,(fun j => nomatch j),word []⟩
  obtain ⟨d,hr,hh,hout⟩ := FormulaTokenCount.scan sep src none c [] rfl
    (Tape.init_move_right_hasBinarySuffix src) Tape.init_nil_move_right_hasBinaryPrefix_nil
  obtain ⟨hi,_,ho⟩ := FormulaLookupFrame.start_frame _ hr
    ((Tape.StartInvariant.init_ofBool src).move .right) (by intro j; exact Fin.elim0 j)
    ((Tape.StartInvariant.init_ofBool []).move .right)
  have hb := (head_le_start_add_of_reachesIn _ hr).1
  refine ⟨d,src.length+1,le_rfl,hr,hh,input_cells_eq_of_reachesIn hr,hi,?_,?_⟩
  · change d.input.head ≤ 1+(src.length+1) at hb
    omega
  · exact FormulaLookupFrame.prefix_acc _ _ (by simpa [FormulaTokenCount.countBits] using hout) ho.1

theorem scanned_stable (sep : Bool) (src : List Bool) : ∀ inp work out,
    scanned sep src inp work out → scanned sep src (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  rintro inp work out ⟨hc,hi,hb,ho⟩
  rw [transitionTape_eq_self ho.parked.read_ne_start]
  refine ⟨(Tape.move_cells _ _).trans hc,hi.move _,?_,ho⟩
  by_cases hr : inp.read = Γ.start
  · have hz : inp.head = 0 := by
      by_contra hn
      exact hi.read_ne_start (by omega) hr
    simp [transitionInput,idleDir,hr,Tape.move,hz]
  · simpa [transitionInput,idleDir,hr,Tape.move] using hb

theorem restore_input (sep : Bool) (src : List Bool) :
    (rewindInputTM (n := 0)).HoareTime (scanned sep src)
      (EmitPred (word src) (fun j => nomatch j) (FormulaTokenCount.countBits sep src))
      (src.length+4) := by
  let P : Complexity.TM.TapePred 0 := fun inp _ out => inp.cells = (word src).cells ∧
    OutAcc (FormulaTokenCount.countBits sep src) out
  have h := rewindInputTM_hoareTime_frame (src.length+2) (P := P) (by
    rintro inp work out inp' work' out' ⟨hc,ho⟩ he _ rfl rfl
    exact ⟨he.trans hc,ho⟩)
  apply h.consequence
  · rintro inp work out ⟨hc,hi,hb,ho⟩
    exact ⟨hi.1,hi.2,hb,ho.parked.read_ne_start,ho.parked.1,
      (by intro j; exact Fin.elim0 j),hc,ho⟩
  · rintro inp work out ⟨hh,hc,ho⟩
    exact ⟨Tape.ext hh hc,(by funext j; exact Fin.elim0 j),ho⟩
  · omega

def count (sep : Bool) : TM 0 := seqTM (FormulaTokenCount.machine sep) rewindInputTM

theorem count_hoare (sep : Bool) (src : List Bool) : (count sep).HoareTime
    (EmitPred (word src) (fun j => nomatch j) [])
    (EmitPred (word src) (fun j => nomatch j) (FormulaTokenCount.countBits sep src))
    (2*src.length+6) := by
  have h := seqTM_hoareTime _ _ (scan_hoare sep src) (scanned_stable sep src) (restore_input sep src)
  exact h.mono_bound (by omega)

def result (sep : Bool) (src emitted : List Bool) : Complexity.TM.TapePred 1 := fun inp work out =>
  inp = word src ∧ OutAcc (FormulaTokenCount.countBits sep src) (work 0) ∧ OutAcc emitted out

theorem routed_hoare (sep : Bool) (src emitted : List Bool) :
    (count sep).retargetOutput.HoareTime (EmitPred (word src) (fun _ => word []) emitted)
      (result sep src emitted) (2*src.length+6) := by
  rintro inp work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hr,hh,hi,_,hout⟩ := count_hoare sep src _ _ _ ⟨rfl,rfl,outAcc_nil_init⟩
  have hs := VerifierOutputRouting.run_frame _ out ho.parked.read_ne_start hr
  refine ⟨VerifierOutputRouting.wrap _ out d,t,ht,?_,hh,hi,hout,ho⟩
  simpa [VerifierOutputRouting.wrap,retargetCfg,retargetOutput,word,List.map_nil,Tape.move] using hs

theorem result_stable (sep : Bool) (src emitted : List Bool) : ∀ inp work out,
    result sep src emitted inp work out → result sep src emitted (transitionInput inp)
      (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have hold := h
  obtain ⟨hi,hc,ho⟩ := h
  have hp : ∀ j, Parked (work j) := by intro j; fin_cases j; exact hc.parked
  obtain ⟨hin,hw,hout⟩ := phaseTransition_eq_self_of_reads_ne_start
    (hi ▸ (word_parked src).read_ne_start) (fun j => (hp j).read_ne_start) ho.parked.read_ne_start
  simpa only [hin,hw,hout] using hold

theorem rewind_hoare (sep : Bool) (src emitted : List Bool) :
    (rewindWorkTM (0 : Fin 1)).HoareTime (result sep src emitted)
      (EmitPred (word src) (fun _ => word (FormulaTokenCount.countBits sep src)) emitted)
      ((FormulaTokenCount.countBits sep src).length+3) := by
  rintro inp work out ⟨rfl,hc,ho⟩
  have hp : ∀ j, Parked (work j) := by intro j; fin_cases j; exact hc.parked
  obtain ⟨d,t,ht,hr,hh,hi,hw,hout⟩ := VerifierPairRestore.restore_word (0 : Fin 1)
    (FormulaTokenCount.countBits sep src) emitted (word src) work (word_parked src) hp hc
    _ _ _ ⟨rfl,rfl,ho⟩
  refine ⟨d,t,ht,hr,hh,hi,?_,hout⟩
  rw [hw]
  funext j
  fin_cases j
  simp

theorem count_length (sep : Bool) (src : List Bool) :
    (FormulaTokenCount.countBits sep src).length ≤ src.length+1 := by
  obtain ⟨d,t,ht,hr,_,_,_,_,ho⟩ := scan_hoare sep src _ _ _ ⟨rfl,rfl,outAcc_nil_init⟩
  have hb := (head_le_start_add_of_reachesIn _ hr).2.1
  change d.output.head ≤ 1+t at hb
  rw [ho.1] at hb
  omega

def machine (sep : Bool) : TM 1 := seqTM (count sep).retargetOutput (rewindWorkTM 0)

/-- Count clauses or occurrences into a real unary tape, restoring the source and output. -/
theorem ready_hoare (sep : Bool) (src emitted : List Bool) : (machine sep).HoareTime
    (EmitPred (word src) (fun _ => word []) emitted)
    (EmitPred (word src) (fun _ => word (FormulaTokenCount.countBits sep src)) emitted)
    (3*src.length+11) := by
  have h := seqTM_hoareTime _ _ (routed_hoare sep src emitted) (result_stable sep src emitted)
    (rewind_hoare sep src emitted)
  apply h.mono_bound
  have hb := count_length sep src
  omega

end UnconstrainedPACDetection.FormulaCountRegisters

module

public import proofs.UnconstrainedPACDetection.VerifierWitnessCounts
public import proofs.UnconstrainedPACDetection.VerifierEqualityCommit

@[expose] public section

namespace UnconstrainedPACDetection.VerifierJointWitness
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierCountPrepare (pairFrame)

abbrev original := VerifierWitnessCounts.machine
def buffered : TM 7 := retargetInput original
def routed : TM 8 := buffered.retargetOutput
def scan : TM 11 := placeWorkTM 3 0 routed

def layout (source : Fin 3 → Tape) (counts : Fin 6 → Tape) (wit verdict : Tape) : Fin 11 → Tape :=
  ![source 0,source 1,source 2,counts 0,counts 1,counts 2,counts 3,counts 4,counts 5,wit,verdict]

def embed (source : Fin 3 → Tape) (inp out : Tape) (c : Cfg 6 original.Q) : Cfg 11 scan.Q :=
  placeWorkCfg routed 3 0 (layout source (fun _ => wordTape []) (wordTape []) (wordTape []))
    (VerifierOutputRouting.wrap buffered out (retargetWrap original inp c))

theorem retarget_run {t : ℕ} {c d : Cfg 6 original.Q}
    (h : original.reachesIn t c d) (hi : c.input.StartInvariant)
    (inp : Tape) (hr : inp.read ≠ .start) :
    buffered.reachesIn t (retargetWrap original inp c) (retargetWrap original inp d) := by
  have hidle : inp.move (idleDir inp.read) = inp := by simp [idleDir,hr,Tape.move]
  induction h with
  | zero => exact .zero
  | step hs _ ih =>
    have hc := input_cells_eq_of_step hs
    have hi' : _ := And.intro (hc ▸ hi.1) (fun j hj => hc ▸ hi.2 j hj)
    have hstep := retargetInput_step_commute original hs inp hi
    rw [hidle] at hstep
    exact .step hstep (ih hi')

def result (bits : List Bool) (source : Fin 3 → Tape) (inp₀ : Tape) (prior committed : Bool) :
    Complexity.TM.TapePred 11 := fun inp work out => inp = inp₀ ∧
    ∃ m n b wit, VerifierWitnessRegisters.Meaning bits m n b ∧ Parked wit ∧
      wit.cells = (wordTape bits).cells ∧
      work = layout source (pairFrame m n true true) wit
        (if committed then wordTape [] else one .start b) ∧
      out = one .start (if committed then b && prior else prior)

theorem scan_hoare (bits : List Bool) (source : Fin 3 → Tape) (inp₀ : Tape) (prior : Bool)
    (hs : ∀ j, (source j).read ≠ .start) (hi : inp₀.read ≠ .start) : scan.HoareTime
    (fun inp work out => inp = inp₀ ∧
      work = layout source (fun _ => wordTape []) (wordTape bits) (wordTape []) ∧ out = one .start prior)
    (result bits source inp₀ prior false) (40*(bits.length+1)^2+2*bits.length+15) := by
  rintro inp work out ⟨hin,hwork,hout⟩
  subst inp; subst work; subst out
  obtain ⟨d,t,ht,hd,hh,hpark,hcells,m,n,b,hmeaning,hdw,hdo⟩ :=
    VerifierWitnessCounts.validation_hoare bits (wordTape bits) (fun _ => wordTape []) (wordTape []) ⟨rfl,rfl,rfl⟩
  have hret := retarget_run hd ((Tape.StartInvariant.init_ofBool bits).move .right) inp₀ hi
  have hout : (one .start prior).read ≠ .start := by change Γ.blank ≠ Γ.start; decide
  have hr := VerifierOutputRouting.run_frame buffered (one .start prior) hout hret
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal routed 3 0
    (layout source (fun _ => wordTape []) (wordTape []) (wordTape [])) hr (by
      intro j hj; fin_cases j
      · exact hs 0
      · exact hs 1
      · exact hs 2
      all_goals simp [placeWorkInMiddle] at hj)
  have he : embed source inp₀ (one .start prior)
      ⟨original.qstart,wordTape bits,fun _ => wordTape [],wordTape []⟩ =
      (⟨scan.qstart,inp₀,layout source (fun _ => wordTape []) (wordTape bits) (wordTape []),one .start prior⟩ :
        Cfg 11 scan.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  change scan.reachesIn t (embed source inp₀ (one .start prior) _) (embed source inp₀ (one .start prior) d) at hp
  rw [he] at hp
  have hdo' : d.output = one .start b := hdo.eq
    (VerifierEntityLoopBody.acc_of_prefix _ _ (VerifierVerdictCommit.one_prefix _ _) rfl)
  refine ⟨_,t,ht,hp,hh,rfl,m,n,b,d.input,hmeaning,hpark,hcells,?_,rfl⟩
  funext j; fin_cases j <;>
    simp [embed,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,VerifierOutputRouting.wrap,
      retargetCfg,retargetWrap,layout,hdw,hdo']

theorem stable (bits : List Bool) (source : Fin 3 → Tape) (inp₀ : Tape) (prior c : Bool)
    (hs : ∀ j, (source j).read ≠ .start) (hi : inp₀.read ≠ .start) :
    ∀ inp work out, result bits source inp₀ prior c inp work out →
      result bits source inp₀ prior c (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have horig := h
  obtain ⟨hin,m,n,b,wit,_,hwit,_,hw,ho⟩ := h
  have hwork : ∀ j, (work j).read ≠ .start := by
    rw [hw]; intro j; fin_cases j
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact (VerifierCountPrepare.pair_parked m n true true 0).read_ne_start
    · exact (VerifierCountPrepare.pair_parked m n true true 1).read_ne_start
    · exact (VerifierCountPrepare.pair_parked m n true true 2).read_ne_start
    · exact (VerifierCountPrepare.pair_parked m n true true 3).read_ne_start
    · exact (VerifierCountPrepare.pair_parked m n true true 4).read_ne_start
    · exact (VerifierCountPrepare.pair_parked m n true true 5).read_ne_start
    · exact hwit.read_ne_start
    · cases c <;> change Γ.blank ≠ Γ.start <;> decide
  have hout : out.read ≠ .start := by rw [ho]; change Γ.blank ≠ Γ.start; decide
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start (hin ▸ hi) hwork hout
  simpa only [hi',hw',ho'] using horig

def commit : TM 11 := placeWorkTM 10 0 VerifierVerdictAnd.machine

theorem commit_hoare (bits : List Bool) (source : Fin 3 → Tape) (inp₀ : Tape) (prior : Bool)
    (hs : ∀ j, (source j).read ≠ .start) (hi : inp₀.read ≠ .start) : commit.HoareTime
    (result bits source inp₀ prior false) (result bits source inp₀ prior true) 2 := by
  rintro inp work out ⟨hin,m,n,b,wit,hm,hp,hc,hw,ho⟩
  subst inp; subst work; subst out
  let base := layout source (pairFrame m n true true) wit (one .start b)
  let c : Cfg 1 (Fin 3) := ⟨0,inp₀,fun _ => one .start b,one .start prior⟩
  let d : Cfg 1 (Fin 3) := ⟨2,inp₀,fun _ => VerifierVerdictAnd.empty .start,one .start (b && prior)⟩
  have hr := VerifierVerdictAnd.run inp₀ hi .start .start b prior
  have hplaced := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierVerdictAnd.machine 10 0 base hr (by
      intro j hj; fin_cases j
      · exact hs 0
      · exact hs 1
      · exact hs 2
      · exact (VerifierCountPrepare.pair_parked m n true true 0).read_ne_start
      · exact (VerifierCountPrepare.pair_parked m n true true 1).read_ne_start
      · exact (VerifierCountPrepare.pair_parked m n true true 2).read_ne_start
      · exact (VerifierCountPrepare.pair_parked m n true true 3).read_ne_start
      · exact (VerifierCountPrepare.pair_parked m n true true 4).read_ne_start
      · exact (VerifierCountPrepare.pair_parked m n true true 5).read_ne_start
      · exact hp.read_ne_start
      · simp [placeWorkInMiddle] at hj)
  have he : placeWorkCfg VerifierVerdictAnd.machine 10 0 base c =
      (⟨commit.qstart,inp₀,base,one .start prior⟩ : Cfg 11 commit.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  change commit.reachesIn 2 (placeWorkCfg VerifierVerdictAnd.machine 10 0 base c)
    (placeWorkCfg VerifierVerdictAnd.machine 10 0 base d) at hplaced
  rw [he] at hplaced
  refine ⟨_,2,le_rfl,hplaced,rfl,rfl,m,n,b,wit,hm,hp,hc,?_,rfl⟩
  funext j; fin_cases j <;> rfl

def machine : TM 11 := seqTM scan commit

theorem validation_hoare (bits : List Bool) (source : Fin 3 → Tape) (inp₀ : Tape) (prior : Bool)
    (hs : ∀ j, (source j).read ≠ .start) (hi : inp₀.read ≠ .start) : machine.HoareTime
    (fun inp work out => inp = inp₀ ∧
      work = layout source (fun _ => wordTape []) (wordTape bits) (wordTape []) ∧ out = one .start prior)
    (result bits source inp₀ prior true) (40*(bits.length+1)^2+2*bits.length+18) := by
  have h := seqTM_hoareTime _ _ (scan_hoare bits source inp₀ prior hs hi)
    (stable bits source inp₀ prior false hs hi) (commit_hoare bits source inp₀ prior hs hi)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierJointWitness

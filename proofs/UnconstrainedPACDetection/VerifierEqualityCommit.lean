module

public import proofs.UnconstrainedPACDetection.VerifierEqualityFrame
public import proofs.UnconstrainedPACDetection.VerifierVerdictCommit

@[expose] public section

namespace UnconstrainedPACDetection.VerifierEqualityCommit
open Complexity Complexity.TM
open VerifierVerdictAnd (one empty)
open VerifierBufferedProduct (wordTape)

abbrev sourceMachine := VerifierBinaryEquality.machine
def buffered : TM 2 := retargetInput sourceMachine
def scan : TM 3 := buffered.retargetOutput
def commit : TM 3 := placeWorkTM 2 0 VerifierVerdictAnd.machine
def machine : TM 3 := seqTM scan commit

theorem retarget_run {t : ℕ} {c d : Cfg 1 sourceMachine.Q}
    (h : sourceMachine.reachesIn t c d) (hi : c.input.StartInvariant)
    (realInput : Tape) (hr : realInput.read ≠ .start) :
    buffered.reachesIn t (retargetWrap sourceMachine realInput c)
      (retargetWrap sourceMachine realInput d) := by
  have hidle : realInput.move (idleDir realInput.read) = realInput := by
    simp [idleDir,hr,Tape.move]
  induction h with
  | zero => exact .zero
  | step hs _ ih =>
    have hc := input_cells_eq_of_step hs
    have hi' : _ := And.intro (hc ▸ hi.1) (fun j hj => hc ▸ hi.2 j hj)
    have hstep := retargetInput_step_commute sourceMachine hs realInput hi
    rw [hidle] at hstep
    exact .step hstep (ih hi')

def before (xs ys : List Bool) (v : Bool) (inp₀ : Tape) : Complexity.TM.TapePred 3 :=
  fun inp work out => inp = inp₀ ∧
    work = ![wordTape ys,wordTape xs,wordTape []] ∧ out = one .start v

def middle (xs ys : List Bool) (v : Bool) (inp₀ : Tape) : Complexity.TM.TapePred 3 :=
  fun inp work out => inp = inp₀ ∧
    (work 0).HasBinarySuffix [] ∧ (work 1).HasBinarySuffix [] ∧
    (work 0).cells = (wordTape ys).cells ∧ (work 1).cells = (wordTape xs).cells ∧
    work 2 = one .start (VerifierBinaryEquality.compare true xs ys) ∧ out = one .start v

def after (xs ys : List Bool) (v : Bool) (inp₀ : Tape) : Complexity.TM.TapePred 3 :=
  fun inp work out => inp = inp₀ ∧
    (work 0).HasBinarySuffix [] ∧ (work 1).HasBinarySuffix [] ∧
    (work 0).cells = (wordTape ys).cells ∧ (work 1).cells = (wordTape xs).cells ∧
    work 2 = wordTape [] ∧
    out = one .start (VerifierBinaryEquality.compare true xs ys && v)

theorem scan_hoare (xs ys : List Bool) (v : Bool) (inp₀ : Tape)
    (hi : inp₀.read ≠ .start) :
    scan.HoareTime (before xs ys v inp₀) (middle xs ys v inp₀)
      (max xs.length ys.length+1) := by
  rintro inp work out ⟨hin,hwork,hout₀⟩
  subst inp; subst work; subst out
  let s : Cfg 1 sourceMachine.Q :=
    ⟨some true,wordTape xs,fun _ => wordTape ys,wordTape []⟩
  obtain ⟨d,hd,hh,hout,hxe,hye,hxc,hyc⟩ :=
    VerifierBinaryEquality.boundary_frame xs ys true s rfl
      (Tape.init_move_right_hasBinaryString xs).hasBinarySuffix
      (Tape.init_move_right_hasBinaryString ys).hasBinarySuffix []
      Tape.init_nil_move_right_hasBinaryPrefix_nil
  have hb := retarget_run hd ((Tape.StartInvariant.init_ofBool xs).move .right) inp₀ hi
  have hr := VerifierOutputRouting.run_frame buffered (one .start v)
    (by change Γ.blank ≠ Γ.start; decide) hb
  let embed := fun z : Cfg 1 sourceMachine.Q =>
    VerifierOutputRouting.wrap buffered (one .start v) (retargetWrap sourceMachine inp₀ z)
  have he : embed s = (⟨scan.qstart,inp₀,
      ![wordTape ys,wordTape xs,wordTape []],one .start v⟩ : Cfg 3 scan.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  have hozero := output_cells_zero_eq_start_of_reachesIn hd rfl
  refine ⟨embed d,_,le_rfl,?_,hh,rfl,hye,hxe,hyc,hxc,?_,rfl⟩
  · change scan.reachesIn _ (embed s) (embed d) at hr
    simpa only [he] using hr
  · change d.output = _
    rw [VerifierVerdictAnd.prefix_eq d.output _ (by simpa using hout),hozero]

theorem middle_stable (xs ys : List Bool) (v : Bool) (inp₀ : Tape)
    (hi : inp₀.read ≠ .start) :
    ∀ inp work out, middle xs ys v inp₀ inp work out →
      middle xs ys v inp₀ (transitionInput inp)
        (fun j => transitionTape (work j)) (transitionTape out) := by
  intro inp work out h
  have horig := h
  obtain ⟨hin,h0,h1,hc0,hc1,h2,hout⟩ := h
  have hw : ∀ j, (work j).read ≠ .start := by
    intro j; fin_cases j
    · exact h0.read_ne_start
    · exact h1.read_ne_start
    · change (work 2).read ≠ .start
      rw [h2]; change Γ.blank ≠ Γ.start; decide
  have ho : out.read ≠ .start := by rw [hout]; change Γ.blank ≠ Γ.start; decide
  obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start (hin ▸ hi) hw ho
  simpa only [hi',hw',ho'] using horig

theorem commit_hoare (xs ys : List Bool) (v : Bool) (inp₀ : Tape)
    (hi : inp₀.read ≠ .start) :
    commit.HoareTime (middle xs ys v inp₀) (after xs ys v inp₀) 2 := by
  rintro inp work out ⟨hin,h0,h1,hc0,hc1,h2,hout⟩
  subst inp; subst out
  let b := VerifierBinaryEquality.compare true xs ys
  let c : Cfg 1 (Fin 3) := ⟨0,inp₀,fun _ => one .start b,one .start v⟩
  let d : Cfg 1 (Fin 3) := ⟨2,inp₀,fun _ => empty .start,one .start (b && v)⟩
  have hr := VerifierVerdictAnd.run inp₀ hi .start .start b v
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    VerifierVerdictAnd.machine 2 0 work hr (by
      intro j hj
      fin_cases j
      · exact h0.read_ne_start
      · exact h1.read_ne_start
      · simp [placeWorkInMiddle] at hj)
  have he : placeWorkCfg VerifierVerdictAnd.machine 2 0 work c =
      (⟨commit.qstart,inp₀,work,one .start v⟩ : Cfg 3 commit.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,c,h2,b]
    · rfl
  refine ⟨placeWorkCfg VerifierVerdictAnd.machine 2 0 work d,2,le_rfl,?_,rfl,
    rfl,h0,h1,hc0,hc1,?_,rfl⟩
  · change commit.reachesIn 2 (placeWorkCfg VerifierVerdictAnd.machine 2 0 work c)
      (placeWorkCfg VerifierVerdictAnd.machine 2 0 work d) at hp
    simpa only [he] using hp
  · exact VerifierVerdictCommit.empty_start

theorem validation_hoare (xs ys : List Bool) (v : Bool) (inp₀ : Tape)
    (hi : inp₀.read ≠ .start) :
    machine.HoareTime (before xs ys v inp₀) (after xs ys v inp₀)
      (max xs.length ys.length+4) := by
  have h := seqTM_hoareTime _ _ (scan_hoare xs ys v inp₀ hi)
    (middle_stable xs ys v inp₀ hi) (commit_hoare xs ys v inp₀ hi)
  simpa [machine,Nat.add_assoc] using h

theorem verdict_iff (xs ys : List Bool) (v : Bool) :
    (VerifierBinaryEquality.compare true xs ys && v) = true ↔
      BinaryFields.readNat xs = BinaryFields.readNat ys ∧ v = true := by
  rw [Bool.and_eq_true,VerifierBinaryEquality.equality_iff]
  exact and_congr eq_comm Iff.rfl

end UnconstrainedPACDetection.VerifierEqualityCommit

module

public import proofs.UnconstrainedPACDetection.VerifierFlowFlagSemantics

@[expose] public section

namespace UnconstrainedPACDetection.VerifierFlowRestart
open Complexity Complexity.TM
open VerifierAccumulate (markerDir)
open VerifierVerdictAnd (one)
open VerifierActivationScan (flag)
open VerifierBufferedProduct (wordTape)
open VerifierMaskRestore (fixed)

def action (q : Fin 3) (i : Γ) : Fin 3 × Dir3 × Dir3 :=
  if q = 0 then if i = .zero then (2,.right,.left) else (1,.right,.stay)
  else (0,.right,.stay)

def skip : TM 1 where
  Q := Fin 3
  qstart := 0
  qhalt := 2
  δ := fun q i w o =>
    let a := action q i
    (a.1,fun j => readBackWrite (w j),readBackWrite o,markerDir i a.2.1,
      fun j => idleDir (w j),markerDir o a.2.2)
  δ_right_of_start := by
    intro q i w o
    exact ⟨fun h => by simp [markerDir,h],fun _ => idleDir_right_of_start,
      fun h => by simp [markerDir,h]⟩

def moved (c : Cfg 1 (Fin 3)) (q : Fin 3) : Cfg 1 (Fin 3) :=
  ⟨q,c.input.move .right,c.work,c.output⟩

theorem step_keep (c : Cfg 1 (Fin 3)) (q : Fin 3) (hn : c.state ≠ 2)
    (hi : c.input.read ≠ .start) (hw : ∀ j, (c.work j).read ≠ .start)
    (ho : c.output.read ≠ .start) (ha : action c.state c.input.read = (q,.right,.stay)) :
    skip.step c = some (moved c q) := by
  simp only [TM.step,skip,hn,↓reduceIte,ha,markerDir,ite_eq_right hi,ite_eq_right ho]
  congr 1
  apply Cfg.ext
  · rfl
  · rfl
  · funext j; exact transitionTape_eq_self (hw j)
  · exact writeAndMove_readBack _ ho .stay

theorem skip_run (mask tail : List Bool) (c : Cfg 1 (Fin 3)) (m : Γ) (a : Bool)
    (hq : c.state = 0) (hi : c.input.HasBinarySuffix (BinaryFields.encodeField mask ++ tail))
    (hw : ∀ j, (c.work j).read ≠ .start) (ho : c.output = one m a) :
    ∃ d, skip.reachesIn (2*mask.length+1) c d ∧ d.state = (2 : Fin 3) ∧
      d.input.HasBinarySuffix tail ∧ d.input.head = c.input.head+2*mask.length+1 ∧
      d.input.cells = c.input.cells ∧ d.work = c.work ∧ d.output = flag m a := by
  induction mask generalizing c with
  | nil =>
    have hi' : c.input.HasBinarySuffix (false :: tail) := hi
    let d : Cfg 1 (Fin 3) := ⟨2,c.input.move .right,c.work,flag m a⟩
    have hs : skip.step c = some d := by
      simp only [TM.step,skip,action,hq,hi'.read_cons,ho]
      simp only [show (0 : Fin 3) ≠ 2 by decide,↓reduceIte,Γ.ofBool,markerDir]
      congr 1
      apply Cfg.ext
      · rfl
      · rfl
      · funext j; exact transitionTape_eq_self (hw j)
      · have h : (one m a).read ≠ .start := by change Γ.blank ≠ Γ.start; decide
        exact writeAndMove_readBack _ h .left
    exact ⟨d,.step hs .zero,rfl,hi'.move_right_cons,rfl,rfl,rfl,rfl⟩
  | cons b mask ih =>
    have hi' : c.input.HasBinarySuffix (true :: b :: (BinaryFields.encodeField mask ++ tail)) := hi
    have hor : c.output.read ≠ .start := by rw [ho]; change Γ.blank ≠ Γ.start; decide
    let c1 := moved c 1
    have hs1 := step_keep c 1 (by rw [hq]; decide) hi.read_ne_start hw hor
      (by simp [action,hq,hi'.read_cons,Γ.ofBool])
    have hi1 : c1.input.HasBinarySuffix (b :: (BinaryFields.encodeField mask ++ tail)) := hi'.move_right_cons
    let c2 := moved c1 0
    have hs2 := step_keep c1 0 (by change (1 : Fin 3) ≠ 2; decide) hi1.read_ne_start hw hor
      (by simp [action,c1,moved])
    obtain ⟨d,hd,hdq,hdi,hdh,hdc,hdw,hdo⟩ := ih c2 rfl hi1.move_right_cons hw ho
    refine ⟨d,?_,hdq,hdi,?_,hdc,hdw,hdo⟩
    · convert TM.reachesIn.step hs1 (TM.reachesIn.step hs2 hd) using 1
    · simp only [c2,c1,moved,Tape.move] at hdh
      simp only [List.length_cons]; omega

theorem input_hoare (bits : List Bool) (inp wt out : Tape)
    (hc : inp.cells = (wordTape bits).cells)
    (hw : wt.read ≠ .start) (hwh : 1 ≤ wt.head)
    (ho : out.read ≠ .start) (hoh : 1 ≤ out.head) :
    (rewindInputTM (n := 1)).HoareTime (fixed inp wt out)
      (fixed (wordTape bits) wt out) (inp.head+2) := by
  let P : Complexity.TM.TapePred 1 := fun i w o =>
    i.cells = inp.cells ∧ w = (fun _ => wt) ∧ o = out
  have hm := (Tape.StartInvariant.init_ofBool bits).move .right
  have hr := rewindInputTM_hoareTime_frame (n := 1) inp.head (P := P) (by
    rintro i w o i' w' o' ⟨hin,hwork,hout⟩ hin' _ hw' ho'
    exact ⟨hin'.trans hin,hw'.trans hwork,ho'.trans hout⟩)
  rintro i w o ⟨hin,hwork,hout⟩
  subst i; subst w; subst o
  obtain ⟨d,t,ht,hd,hh,hh1,hcells,hw',ho'⟩ := hr inp (fun _ => wt) out
    ⟨by rw [hc]; exact hm.1,by intro j hj; rw [hc]; exact hm.2 j hj,
      le_rfl,ho,hoh,(fun _ => ⟨hw,hwh⟩),rfl,rfl,rfl⟩
  exact ⟨d,t,ht,hd,hh,Tape.ext hh1 (hcells.trans hc),hw',ho'⟩

def flowInput (mask tail : List Bool) : Tape :=
  ⟨2*mask.length+2,(wordTape (BinaryFields.encodeField mask ++ tail)).cells⟩

theorem skip_hoare (mask tail : List Bool) (wt : Tape) (hw : wt.read ≠ .start) (m : Γ) (a : Bool) :
    skip.HoareTime (fixed (wordTape (BinaryFields.encodeField mask ++ tail)) wt (one m a))
      (fixed (flowInput mask tail) wt (flag m a)) (2*mask.length+1) := by
  rintro i w o ⟨hin,hwork,hout⟩
  subst i; subst w; subst o
  obtain ⟨d,hd,hh,_,hdh,hdc,hdw,hdo⟩ := skip_run mask tail
    ⟨(0 : Fin 3),wordTape (BinaryFields.encodeField mask ++ tail),fun _ => wt,one m a⟩ m a rfl
    (Tape.init_move_right_hasBinaryString _).hasBinarySuffix (fun _ => hw) rfl
  refine ⟨d,_,le_rfl,hd,hh,?_,hdw,hdo⟩
  apply Tape.ext
  · change d.input.head = 2*mask.length+2
    change d.input.head = 1+2*mask.length+1 at hdh
    omega
  · exact hdc

def machine : TM 1 := seqTM rewindInputTM skip

theorem restart_hoare (mask tail : List Bool) (inp wt : Tape) (m : Γ) (a : Bool)
    (hc : inp.cells = (wordTape (BinaryFields.encodeField mask ++ tail)).cells)
    (hw : wt.read ≠ .start) (hwh : 1 ≤ wt.head) :
    machine.HoareTime (fixed inp wt (one m a))
      (fixed (flowInput mask tail) wt (flag m a)) (inp.head+2*mask.length+4) := by
  have ho : (one m a).read ≠ .start := by change Γ.blank ≠ Γ.start; decide
  have stable : ∀ i w o, fixed (wordTape (BinaryFields.encodeField mask ++ tail)) wt (one m a) i w o →
      fixed (wordTape (BinaryFields.encodeField mask ++ tail)) wt (one m a)
        (transitionInput i) (fun j => transitionTape (w j)) (transitionTape o) := by
    rintro i w o ⟨hin,hwork,hout⟩
    subst i; subst w; subst o
    exact phaseTransition_eq_self_of_reads_ne_start
      (Tape.init_move_right_hasBinaryString _).hasBinarySuffix.read_ne_start (fun _ => hw) ho
  exact (seqTM_hoareTime _ _ (input_hoare _ inp wt (one m a) hc hw hwh ho (by change 1 ≤ 2; decide)) stable
    (skip_hoare mask tail wt hw m a)).mono_bound (by omega)

theorem flowInput_suffix (mask tail : List Bool) : (flowInput mask tail).HasBinarySuffix tail := by
  obtain ⟨d,hd,hh,hdi,hdh,hdc,hdw,hdo⟩ := skip_run mask tail
    ⟨(0 : Fin 3),wordTape (BinaryFields.encodeField mask ++ tail),fun _ => wordTape [],one .start true⟩
    .start true rfl (Tape.init_move_right_hasBinaryString _).hasBinarySuffix
    (fun _ => (Tape.init_move_right_hasBinaryString _).hasBinarySuffix.read_ne_start) rfl
  have he : d.input = flowInput mask tail := by
    apply Tape.ext
    · change d.input.head = 2*mask.length+2
      change d.input.head = 1+2*mask.length+1 at hdh
      omega
    · exact hdc
  rwa [he] at hdi

end UnconstrainedPACDetection.VerifierFlowRestart

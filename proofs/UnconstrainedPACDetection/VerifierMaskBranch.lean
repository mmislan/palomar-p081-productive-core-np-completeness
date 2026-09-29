module

public import proofs.UnconstrainedPACDetection.VerifierMaskRouting
public import proofs.UnconstrainedPACDetection.VerifierEntityStep

@[expose] public section

/-! A scratch-bit conditional which preserves the cumulative output. -/
namespace UnconstrainedPACDetection.VerifierMaskBranch
open Complexity Complexity.TM
open VerifierAccumulate (markerDir)

def machine (yes no : TM 13) : TM 13 :=
  haveI : Fintype yes.Q := yes.finQ
  haveI : DecidableEq yes.Q := yes.decEq
  haveI : Fintype no.Q := no.finQ
  haveI : DecidableEq no.Q := no.decEq
  { Q := Fin 3 ⊕ (yes.Q ⊕ no.Q)
    qstart := .inl 0
    qhalt := .inl 2
    δ := fun q i w o => match q with
      | .inl q => if q = 0 then
          (.inl 1,fun j => readBackWrite (w j),readBackWrite o,idleDir i,
            fun j => if j = 11 then markerDir (w j) .left else idleDir (w j),idleDir o)
        else
          (if w 11 = .one then .inr (.inl yes.qstart) else .inr (.inr no.qstart),
            fun j => if j = 11 then .blank else readBackWrite (w j),readBackWrite o,
            idleDir i,fun j => idleDir (w j),idleDir o)
      | .inr (.inl q) => if q = yes.qhalt then (.inl 2,fun j => readBackWrite (w j),readBackWrite o,idleDir i,fun j => idleDir (w j),idleDir o) else
          let a := yes.δ q i w o
          (.inr (.inl a.1),a.2)
      | .inr (.inr q) => if q = no.qhalt then (.inl 2,fun j => readBackWrite (w j),readBackWrite o,idleDir i,fun j => idleDir (w j),idleDir o) else
          let a := no.δ q i w o
          (.inr (.inr a.1),a.2)
    δ_right_of_start := by
      intro q i w o
      rcases q with q | q
      · dsimp only
        by_cases hq : q = 0
        · simp only [hq,↓reduceIte]
          refine ⟨idleDir_right_of_start,?_,idleDir_right_of_start⟩
          intro j h
          split
          · simp [markerDir,h]
          · exact idleDir_right_of_start h
        · simp only [hq,↓reduceIte]
          exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
      · rcases q with q | q
        · dsimp only
          by_cases hq : q = yes.qhalt
          · simp only [hq,↓reduceIte]; exact rightOfStart_allIdle i w o
          · simp only [hq,↓reduceIte]; exact yes.δ_right_of_start q i w o
        · dsimp only
          by_cases hq : q = no.qhalt
          · simp only [hq,↓reduceIte]; exact rightOfStart_allIdle i w o
          · simp only [hq,↓reduceIte]; exact no.δ_right_of_start q i w o }

def yesWrap (yes no : TM 13) (c : Cfg 13 yes.Q) : Cfg 13 (machine yes no).Q :=
  ⟨.inr (.inl c.state),c.input,c.work,c.output⟩
def noWrap (yes no : TM 13) (c : Cfg 13 no.Q) : Cfg 13 (machine yes no).Q :=
  ⟨.inr (.inr c.state),c.input,c.work,c.output⟩

theorem yes_run (yes no : TM 13) {t : ℕ} {c d : Cfg 13 yes.Q}
    (h : yes.reachesIn t c d) :
    (machine yes no).reachesIn t (yesWrap yes no c) (yesWrap yes no d) := by
  apply reachesIn_map (yesWrap yes no) _ h
  intro c c' hs
  have hn := state_ne_qhalt_of_step hs
  simp only [TM.step,hn,↓reduceIte,Option.some.injEq] at hs
  subst c'
  simp [TM.step,machine,yesWrap,hn]

theorem no_run (yes no : TM 13) {t : ℕ} {c d : Cfg 13 no.Q}
    (h : no.reachesIn t c d) :
    (machine yes no).reachesIn t (noWrap yes no c) (noWrap yes no d) := by
  apply reachesIn_map (noWrap yes no) _ h
  intro c c' hs
  have hn := state_ne_qhalt_of_step hs
  simp only [TM.step,hn,↓reduceIte,Option.some.injEq] at hs
  subst c'
  simp [TM.step,machine,noWrap,hn]

def branchStart (yes no : TM 13) (b : Bool) (inp : Tape) (work : Fin 13 → Tape) (out : Tape) :
    Cfg 13 (machine yes no).Q :=
  ⟨if b then .inr (.inl yes.qstart) else .inr (.inr no.qstart),inp,work,out⟩

/-- Read a one-bit scratch prefix and erase it before either branch starts. -/
theorem dispatch (yes no : TM 13) (b : Bool) (inp out : Tape) (frame : Fin 13 → Tape)
    (hi : inp.read ≠ .start) (ho : out.read ≠ .start)
    (hf : ∀ j, (frame j).read ≠ .start)
    (hblank : frame 11 = VerifierBufferedProduct.wordTape []) :
    (machine yes no).reachesIn 2
      ⟨(machine yes no).qstart,inp,
        Function.update frame 11 (VerifierVerdictAnd.one .start b),out⟩
      (branchStart yes no b inp frame out) := by
  let c0 : Cfg 13 (machine yes no).Q :=
    ⟨.inl 0,inp,Function.update frame 11 (VerifierVerdictAnd.one .start b),out⟩
  let c1 : Cfg 13 (machine yes no).Q :=
    ⟨.inl 1,inp,Function.update frame 11
      ({VerifierVerdictAnd.one .start b with head := 1} : Tape),out⟩
  have hs1 : (machine yes no).step c0 = some c1 := by
    simp only [TM.step,machine,c0,Sum.inl.injEq,show (0 : Fin 3) ≠ 2 by decide,↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · exact transitionInput_eq_self hi
    · funext j
      by_cases hj : j = 11
      · subst j
        simp [c1,Function.update_self,VerifierVerdictAnd.one,markerDir,Tape.read,
          readBackWrite,Tape.writeAndMove,Tape.write,Tape.move]
      · simp only [Function.update_of_ne hj,ite_eq_right hj,c1]
        exact transitionTape_eq_self (hf j)
    · exact transitionTape_eq_self ho
  have hs2 : (machine yes no).step c1 = some (branchStart yes no b inp frame out) := by
    simp only [TM.step,machine,c1,Sum.inl.injEq,show (1 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 0 by decide,↓reduceIte,Function.update_self]
    congr 1
    apply Cfg.ext
    · cases b <;> rfl
    · exact transitionInput_eq_self hi
    · funext j
      by_cases hj : j = 11
      · subst j
        simp only [Function.update_self,↓reduceIte]
        change ({VerifierVerdictAnd.one .start b with head := 1} : Tape).writeAndMove
          .blank (idleDir (Γ.ofBool b)) = frame 11
        have hb : idleDir (Γ.ofBool b) = .stay := by cases b <;> rfl
        rw [hb,VerifierVerdictAnd.clear_one,hblank]
        rfl
      · simp only [Function.update_of_ne hj,ite_eq_right hj,branchStart]
        exact transitionTape_eq_self (hf j)
    · exact transitionTape_eq_self ho
  exact .step hs1 (.step hs2 .zero)

theorem finish_yes (yes no : TM 13) (d : Cfg 13 yes.Q) (hh : yes.halted d)
    (hi : d.input.read ≠ .start) (hw : ∀ j, (d.work j).read ≠ .start)
    (ho : d.output.read ≠ .start) :
    (machine yes no).reachesIn 1 (yesWrap yes no d)
      ⟨(machine yes no).qhalt,d.input,d.work,d.output⟩ := by
  have hs : (machine yes no).step (yesWrap yes no d) =
      some ⟨(machine yes no).qhalt,d.input,d.work,d.output⟩ := by
    simp only [TM.step,machine,yesWrap,Sum.inr_ne_inl,↓reduceIte,hh]
    congr 1
    apply Cfg.ext
    · rfl
    · exact transitionInput_eq_self hi
    · funext j; exact transitionTape_eq_self (hw j)
    · exact transitionTape_eq_self ho
  exact .step hs .zero

theorem finish_no (yes no : TM 13) (d : Cfg 13 no.Q) (hh : no.halted d)
    (hi : d.input.read ≠ .start) (hw : ∀ j, (d.work j).read ≠ .start)
    (ho : d.output.read ≠ .start) :
    (machine yes no).reachesIn 1 (noWrap yes no d)
      ⟨(machine yes no).qhalt,d.input,d.work,d.output⟩ := by
  have hs : (machine yes no).step (noWrap yes no d) =
      some ⟨(machine yes no).qhalt,d.input,d.work,d.output⟩ := by
    simp only [TM.step,machine,noWrap,Sum.inr_ne_inl,↓reduceIte,hh]
    congr 1
    apply Cfg.ext
    · rfl
    · exact transitionInput_eq_self hi
    · funext j; exact transitionTape_eq_self (hw j)
    · exact transitionTape_eq_self ho
  exact .step hs .zero

/-- Uniform execution of the scratch-selected branch, including dispatch,
scratch cleanup, and the common terminal transition. -/
theorem execute (yes no : TM 13) (b : Bool) (inp out : Tape) (frame : Fin 13 → Tape)
    (hi : inp.read ≠ .start) (ho : out.read ≠ .start)
    (hf : ∀ j, (frame j).read ≠ .start)
    (hblank : frame 11 = VerifierBufferedProduct.wordTape [])
    {t : ℕ} {d : Cfg 13 (if b then yes else no).Q}
    (hd : (if b then yes else no).reachesIn t
      ⟨(if b then yes else no).qstart,inp,frame,out⟩ d)
    (hh : (if b then yes else no).halted d)
    (hdi : d.input.read ≠ .start) (hdw : ∀ j, (d.work j).read ≠ .start)
    (hdo : d.output.read ≠ .start) :
    (machine yes no).reachesIn (t+3)
      ⟨(machine yes no).qstart,inp,
        Function.update frame 11 (VerifierVerdictAnd.one .start b),out⟩
      ⟨(machine yes no).qhalt,d.input,d.work,d.output⟩ := by
  have first := dispatch yes no b inp out frame hi ho hf hblank
  cases b
  · have middle := no_run yes no hd
    have last := finish_no yes no d hh hdi hdw hdo
    have h := (machine yes no).reachesIn_trans first ((machine yes no).reachesIn_trans middle last)
    convert h using 1; omega
  · have middle := yes_run yes no hd
    have last := finish_yes yes no d hh hdi hdw hdo
    have h := (machine yes no).reachesIn_trans first ((machine yes no).reachesIn_trans middle last)
    convert h using 1; omega

end UnconstrainedPACDetection.VerifierMaskBranch


module

public import proofs.UnconstrainedPACDetection.VerifierValidatedRun
public import proofs.UnconstrainedPACDetection.VerifierRawRejection

@[expose] public section

namespace UnconstrainedPACDetection.VerifierRawBranch
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierAccumulate (markerDir)

abbrev body := VerifierValidatedRun.machine

def machine : TM 30 where
  Q := Bool ⊕ body.Q
  qstart := .inl false
  qhalt := .inr body.qhalt
  δ := fun q i w o => match q with
    | .inl phase =>
      (if phase then .inr (if w 29 = .one then body.qstart else body.qhalt) else .inl true,
        fun j => readBackWrite (w j),
        if phase && decide (w 29 ≠ .one) then .zero else readBackWrite o,
        idleDir i,fun j => if j = 29 then (if phase then .right else markerDir (w j) .left)
          else idleDir (w j),
        if phase && decide (w 29 ≠ .one) then .right else idleDir o)
    | .inr state =>
      let r := body.δ state i w o
      (.inr r.1,r.2)
  δ_right_of_start := by
    intro q i w o
    cases q with
    | inl phase =>
      refine ⟨idleDir_right_of_start,?_,?_⟩
      · intro j hj
        by_cases h : j = 29
        · subst j
          cases phase
          · simp [markerDir,hj]
          · rfl
        · simp [h,idleDir,hj]
      · intro ho
        split <;> simp_all [idleDir]
    | inr state => exact body.δ_right_of_start state i w o

def embed (c : Cfg 30 body.Q) : Cfg 30 machine.Q :=
  ⟨.inr c.state,c.input,c.work,c.output⟩

theorem step_embed (c : Cfg 30 body.Q) :
    machine.step (embed c) = (body.step c).map embed := by
  by_cases h : c.state = body.qhalt
  · simp [TM.step,machine,embed,h]
    rfl
  · simp [TM.step,machine,embed,h]
    rfl

theorem run_embed {t : Nat} {c d : Cfg 30 body.Q} (h : body.reachesIn t c d) :
    machine.reachesIn t (embed c) (embed d) := by
  induction h with
  | zero => exact .zero
  | @step c _ _ _ hs _ ih => exact .step (by simpa only [hs,Option.map_some] using step_embed c) ih

theorem enter (inp : Tape) (work : Fin 30 → Tape) (v : Bool)
    (hi : inp.read ≠ .start) (hp : ∀ j, Parked (work j)) (hv : work 29 = one .start v) :
    machine.reachesIn 2 ⟨.inl false,inp,work,wordTape []⟩
      (embed ⟨if v then body.qstart else body.qhalt,inp,work,
        if v then wordTape [] else one .start false⟩) := by
  let W := Function.update work 29 ({one .start v with head := 1} : Tape)
  let mid : Cfg 30 machine.Q := ⟨.inl true,inp,W,wordTape []⟩
  have h1 : machine.step ⟨.inl false,inp,work,wordTape []⟩ = some mid := by
    simp only [TM.step,machine,Sum.inl_ne_inr,↓reduceIte,Bool.false_eq_true,Bool.false_and]
    congr 1
    apply Cfg.ext
    · rfl
    · simp [idleDir,hi,Tape.move,mid]
    · funext j
      by_cases hj : j = 29
      · subst j
        change (work 29).writeAndMove (readBackWrite (work 29).read).toΓ
          (markerDir (work 29).read .left) = ({one .start v with head := 1} : Tape)
        rw [hv]
        apply Tape.ext
        · rfl
        · funext k; by_cases hk : k = 2 <;>
            simp [one,Tape.writeAndMove,Tape.write,Tape.read,Tape.move,readBackWrite,markerDir,hk]
      · simpa [mid,W,hj] using (hp j).writeAndMove_readBack_idle
    · exact (VerifierReactionLoop.word_parked []).writeAndMove_readBack_idle
  have h2 : machine.step mid = some
      (embed ⟨if v then body.qstart else body.qhalt,inp,work,
        if v then wordTape [] else one .start false⟩) := by
    simp only [TM.step,machine,mid,Sum.inl_ne_inr,↓reduceIte]
    congr 1
    apply Cfg.ext
    · cases v <;> rfl
    · simp [idleDir,hi,Tape.move,embed]
    · funext j
      by_cases hj : j = 29
      · subst j
        change ({one .start v with head := 1} : Tape).writeAndMove
          (readBackWrite ({one .start v with head := 1} : Tape).read).toΓ .right = work 29
        rw [hv]
        cases v <;> apply Tape.ext
        all_goals try rfl
        all_goals funext k; by_cases hk : k = 1 <;>
          simp [one,Tape.writeAndMove,Tape.write,Tape.read,Tape.move,readBackWrite,Γ.ofBool,hk]
      · simpa [W,hj,embed] using (hp j).writeAndMove_readBack_idle
    · cases v <;> apply Tape.ext
      all_goals try rfl
      all_goals funext k; by_cases hk : k = 1 <;>
        simp [W,wordTape,one,Tape.writeAndMove,Tape.write,Tape.read,Tape.move,Tape.init,
          readBackWrite,Γ.ofBool,embed,hk,idleDir]
  exact .step h1 (.step h2 .zero)

end UnconstrainedPACDetection.VerifierRawBranch

module

public import proofs.UnconstrainedPACDetection.VerifierDimensionCompare

@[expose] public section

namespace UnconstrainedPACDetection.VerifierDimensionGuard
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierAccumulate (markerDir)

abbrev body := VerifierDimensionCompare.bothMachine

def machine : TM 11 where
  Q := Bool ⊕ body.Q
  qstart := .inl false
  qhalt := .inr body.qhalt
  δ := fun q i w o => match q with
    | .inl phase =>
      (if phase then .inr (if o = .one then body.qstart else body.qhalt) else .inl true,
        fun j => readBackWrite (w j),readBackWrite o,idleDir i,
        fun j => idleDir (w j),if phase then .right else markerDir o .left)
    | .inr state =>
      let r := body.δ state i w o
      (.inr r.1,r.2)
  δ_right_of_start := by
    intro q i w o
    cases q with
    | inl phase =>
      refine ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,?_⟩
      intro h; cases phase <;> simp [markerDir,h]
    | inr state => exact body.δ_right_of_start state i w o

def embed (c : Cfg 11 body.Q) : Cfg 11 machine.Q :=
  ⟨.inr c.state,c.input,c.work,c.output⟩

theorem step_embed (c : Cfg 11 body.Q) :
    machine.step (embed c) = (body.step c).map embed := by
  by_cases h : c.state = body.qhalt
  · simp [TM.step,machine,embed,h]
    rfl
  · simp [TM.step,machine,embed,h]
    rfl

theorem run_embed {t : ℕ} {c d : Cfg 11 body.Q} (h : body.reachesIn t c d) :
    machine.reachesIn t (embed c) (embed d) := by
  induction h with
  | zero => exact .zero
  | @step c _ _ _ hs _ ih => exact .step (by simpa only [hs,Option.map_some] using step_embed c) ih

theorem enter (inp : Tape) (work : Fin 11 → Tape) (v : Bool)
    (hi : inp.read ≠ .start) (hp : ∀ j, Parked (work j)) :
    machine.reachesIn 2 ⟨.inl false,inp,work,one .start v⟩
      (embed ⟨if v then body.qstart else body.qhalt,inp,work,one .start v⟩) := by
  let mid : Cfg 11 machine.Q := ⟨.inl true,inp,work,{one .start v with head := 1}⟩
  have h1 : machine.step ⟨.inl false,inp,work,one .start v⟩ = some mid := by
    simp only [TM.step,machine,Sum.inl_ne_inr,↓reduceIte,Bool.false_eq_true]
    congr 1
    apply Cfg.ext
    · rfl
    · simp [idleDir,hi,Tape.move,mid]
    · funext j; exact (hp j).writeAndMove_readBack_idle
    · apply Tape.ext
      · rfl
      · funext i; by_cases h : i = 2 <;>
          simp [one,Tape.writeAndMove,Tape.write,Tape.read,Tape.move,readBackWrite,mid,markerDir,h]
  have h2 : machine.step mid = some
      (embed ⟨if v then body.qstart else body.qhalt,inp,work,one .start v⟩) := by
    simp only [TM.step,machine,mid,Sum.inl_ne_inr,↓reduceIte]
    congr 1
    apply Cfg.ext
    · cases v <;> rfl
    · simp [idleDir,hi,Tape.move,embed]
    · funext j; exact (hp j).writeAndMove_readBack_idle
    · cases v <;> apply Tape.ext
      all_goals try rfl
      all_goals funext i; by_cases h : i = 1 <;>
        simp [one,Tape.writeAndMove,Tape.write,Tape.read,Tape.move,readBackWrite,Γ.ofBool,embed,h]
  exact .step h1 (.step h2 .zero)

theorem rejected_hoare (inp₀ : Tape) (base : Fin 11 → Tape)
    (hi : inp₀.read ≠ .start) (hp : ∀ j, Parked (base j)) : machine.HoareTime
    (fun inp work out => inp = inp₀ ∧ work = base ∧ out = one .start false)
    (fun inp work out => inp = inp₀ ∧ work = base ∧ out = one .start false) 2 := by
  rintro inp work out ⟨hin,hw,ho⟩
  subst inp; subst work; subst out
  exact ⟨_,2,le_rfl,enter inp₀ base false hi hp,rfl,rfl,rfl,rfl⟩

theorem accepted_hoare (x₁ y₁ x₂ y₂ : List Bool) (inp₀ : Tape)
    (base : Fin 11 → Tape) (hi : inp₀.read ≠ .start) (hp : ∀ j, Parked (base j))
    (h3 : base 3 = wordTape y₁) (h1 : base 1 = wordTape x₁)
    (h6 : base 6 = wordTape y₂) (h2 : base 2 = wordTape x₂) (h10 : base 10 = wordTape []) :
    machine.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = base ∧ out = one .start true)
      (VerifierDimensionCompare.bothAfter x₁ y₁ x₂ y₂ true inp₀ base)
      (max x₁.length y₁.length + max x₂.length y₂.length + 11) := by
  rintro inp work out ⟨hin,hw,ho⟩
  subst inp; subst work; subst out
  obtain ⟨d,t,ht,hr,hh,hpost⟩ := VerifierDimensionCompare.both_hoare
    x₁ y₁ x₂ y₂ true inp₀ base hi hp h3 h1 h6 h2 h10 inp₀ base (one .start true) ⟨rfl,rfl,rfl⟩
  have he := enter inp₀ base true hi hp
  have hrun := reachesIn_trans machine he (run_embed hr)
  exact ⟨embed d,2+t,by omega,hrun,congrArg Sum.inr hh,hpost⟩

end UnconstrainedPACDetection.VerifierDimensionGuard

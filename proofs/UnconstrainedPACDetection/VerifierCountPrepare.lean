module

public import proofs.UnconstrainedPACDetection.VerifierUnaryBinary

@[expose] public section

namespace UnconstrainedPACDetection.VerifierCountPrepare
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)

theorem unary_eq_reg (v : ℕ) : wordTape (List.replicate v true) = regTape v := by
  apply Tape.ext
  · rfl
  · funext j
    cases j with
    | zero => rfl
    | succ j =>
      by_cases h : j < v
      · simp [wordTape,Tape.init,Tape.move,regTape,regCells,List.getElem?_replicate,h,
          show j+1 ≤ v by omega,Γ.ofBool]
      · simp [wordTape,Tape.init,Tape.move,regTape,regCells,List.getElem?_replicate,h,
          show ¬ j+1 ≤ v by omega]

def initial (v : ℕ) : Fin 3 → Tape :=
  ![wordTape [],wordTape [],wordTape (List.replicate v true)]

def seed : TM 3 where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w o => (true,fun j => if j = 1 then Γw.one else readBackWrite (w j),
    readBackWrite o,idleDir i,fun j => idleDir (w j),idleDir o)
  δ_right_of_start := by
    intro _ i w o
    exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩

theorem seed_run (v : ℕ) (inp out : Tape) (hi : inp.read ≠ .start) (ho : Parked out) :
    seed.reachesIn 1 ⟨false,inp,initial v,out⟩
      ⟨true,inp,VerifierUnaryBinary.frame 0 (regTape v),out⟩ := by
  have hs : seed.step ⟨false,inp,initial v,out⟩ =
      some ⟨true,inp,VerifierUnaryBinary.frame 0 (regTape v),out⟩ := by
    simp only [TM.step,seed,Bool.false_eq_true,↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · simp [idleDir,hi,Tape.move]
    · funext j; fin_cases j
      · exact (VerifierReactionLoop.word_parked []).writeAndMove_readBack_idle
      · apply Tape.ext
        · rfl
        · funext k; rcases k with _ | (_ | k)
          all_goals
            simp [initial,VerifierUnaryBinary.frame,wordTape,Tape.writeAndMove,Tape.write,
              Tape.move,Tape.init,idleDir,Tape.read,Γ.ofBool]
      · change (wordTape (List.replicate v true)).writeAndMove
          (readBackWrite (wordTape (List.replicate v true)).read).toΓ
          (idleDir (wordTape (List.replicate v true)).read) = regTape v
        rw [(VerifierReactionLoop.word_parked _).writeAndMove_readBack_idle,unary_eq_reg]
    · exact ho.writeAndMove_readBack_idle
  exact .step hs .zero

def machine : TM 3 := seqTM seed VerifierUnaryBinary.machine

theorem conversion_hoare (v : ℕ) (inp₀ : Tape) (hi : Parked inp₀) (b : Bool) :
    machine.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initial v ∧ OutAcc [b] out)
      (fun inp work out => inp = inp₀ ∧ work = VerifierUnaryBinary.frame v (regTape v) ∧ OutAcc [b] out)
      (20*(v+1)^2+2) := by
  have hseed : seed.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initial v ∧ OutAcc [b] out)
      (fun inp work out => inp = inp₀ ∧ work = VerifierUnaryBinary.frame 0 (regTape v) ∧ OutAcc [b] out) 1 := by
    rintro inp work out ⟨hin,hwork,ho⟩
    subst inp; subst work
    exact ⟨_,1,le_rfl,seed_run v inp₀ out hi.read_ne_start ho.parked,rfl,rfl,rfl,ho⟩
  have stable : ∀ inp work out,
      (inp = inp₀ ∧ work = VerifierUnaryBinary.frame 0 (regTape v) ∧ OutAcc [b] out) →
      transitionInput inp = inp₀ ∧
      (fun j => transitionTape (work j)) = VerifierUnaryBinary.frame 0 (regTape v) ∧
      OutAcc [b] (transitionTape out) := by
    rintro inp work out ⟨rfl,rfl,ho⟩
    obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start
      (fun j => (VerifierUnaryBinary.frame_parked 0 _ (parked_regTape v) j).read_ne_start)
      ho.parked.read_ne_start
    exact ⟨hi',hw',by simpa only [ho'] using ho⟩
  have h := seqTM_hoareTime _ _ hseed stable (VerifierUnaryBinary.conversion_hoare v inp₀ hi b)
  exact h.mono_bound (by omega)

theorem bounded_conversion (v L : ℕ) (hv : v ≤ L) (inp₀ : Tape) (hi : Parked inp₀) (b : Bool) :
    machine.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = initial v ∧ OutAcc [b] out)
      (fun inp work out => inp = inp₀ ∧ work = VerifierUnaryBinary.frame v (regTape v) ∧ OutAcc [b] out)
      (20*(L+1)^2+2) :=
  (conversion_hoare v inp₀ hi b).mono_bound (by nlinarith)

def pairFrame (m n : ℕ) (first second : Bool) : Fin 6 → Tape :=
  ![wordTape (if first then VerifierUnaryBinary.digits m else []),
    wordTape (if first then [true] else []),wordTape (List.replicate m true),
    wordTape (if second then VerifierUnaryBinary.digits n else []),
    wordTape (if second then [true] else []),wordTape (List.replicate n true)]

theorem pair_parked (m n : ℕ) (a b : Bool) : ∀ j, Parked (pairFrame m n a b j) := by
  intro j; fin_cases j <;> exact VerifierReactionLoop.word_parked _

def first : TM 6 := placeWorkTM 0 3 machine
def second : TM 6 := placeWorkTM 3 0 machine

theorem first_hoare (m n : ℕ) (inp₀ : Tape) (hi : Parked inp₀) (b : Bool) :
    first.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = pairFrame m n false false ∧ OutAcc [b] out)
      (fun inp work out => inp = inp₀ ∧ work = pairFrame m n true false ∧ OutAcc [b] out)
      (20*(m+1)^2+2) := by
  rintro inp work out ⟨hin,hwork,ho⟩
  subst inp; subst work
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := conversion_hoare m inp₀ hi b inp₀ (initial m) out ⟨rfl,rfl,ho⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal machine 0 3
    (pairFrame m n false false) hd (by intro j _; exact (pair_parked m n false false j).read_ne_start)
  have he : placeWorkCfg machine 0 3 (pairFrame m n false false)
      ⟨machine.qstart,inp₀,initial m,out⟩ =
      (⟨first.qstart,inp₀,pairFrame m n false false,out⟩ : Cfg 6 first.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  rw [he] at hp
  refine ⟨_,t,ht,hp,hh,hdi,?_,hdo⟩
  funext j; fin_cases j <;>
    simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,pairFrame,hdw,
      VerifierUnaryBinary.frame,unary_eq_reg]

theorem second_hoare (m n : ℕ) (inp₀ : Tape) (hi : Parked inp₀) (b : Bool) :
    second.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = pairFrame m n true false ∧ OutAcc [b] out)
      (fun inp work out => inp = inp₀ ∧ work = pairFrame m n true true ∧ OutAcc [b] out)
      (20*(n+1)^2+2) := by
  rintro inp work out ⟨hin,hwork,ho⟩
  subst inp; subst work
  obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := conversion_hoare n inp₀ hi b inp₀ (initial n) out ⟨rfl,rfl,ho⟩
  have hp := placeWorkTM_reachesIn_placeWorkCfg_stable_internal machine 3 0
    (pairFrame m n true false) hd (by intro j _; exact (pair_parked m n true false j).read_ne_start)
  have he : placeWorkCfg machine 3 0 (pairFrame m n true false)
      ⟨machine.qstart,inp₀,initial n,out⟩ =
      (⟨second.qstart,inp₀,pairFrame m n true false,out⟩ : Cfg 6 second.Q) := by
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  rw [he] at hp
  refine ⟨_,t,ht,hp,hh,hdi,?_,hdo⟩
  funext j; fin_cases j <;>
    simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,pairFrame,hdw,
      VerifierUnaryBinary.frame,unary_eq_reg]

def pairMachine : TM 6 := seqTM first second

theorem pair_hoare (m n : ℕ) (inp₀ : Tape) (hi : Parked inp₀) (b : Bool) :
    pairMachine.HoareTime
      (fun inp work out => inp = inp₀ ∧ work = pairFrame m n false false ∧ OutAcc [b] out)
      (fun inp work out => inp = inp₀ ∧ work = pairFrame m n true true ∧ OutAcc [b] out)
      (20*(m+1)^2+20*(n+1)^2+5) := by
  have stable : ∀ inp work out,
      (inp = inp₀ ∧ work = pairFrame m n true false ∧ OutAcc [b] out) →
      transitionInput inp = inp₀ ∧
      (fun j => transitionTape (work j)) = pairFrame m n true false ∧
      OutAcc [b] (transitionTape out) := by
    rintro inp work out ⟨rfl,rfl,ho⟩
    obtain ⟨hi',hw',ho'⟩ := phaseTransition_eq_self_of_reads_ne_start hi.read_ne_start
      (fun j => (pair_parked m n true false j).read_ne_start) ho.parked.read_ne_start
    exact ⟨hi',hw',by simpa only [ho'] using ho⟩
  have h := seqTM_hoareTime _ _ (first_hoare m n inp₀ hi b) stable (second_hoare m n inp₀ hi b)
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierCountPrepare

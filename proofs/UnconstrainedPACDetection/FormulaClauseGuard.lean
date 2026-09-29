module

public import proofs.UnconstrainedPACDetection.VerifierActivationEmit
public import proofs.UnconstrainedPACDetection.FormulaClauseLookup

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseGuard
open Complexity Complexity.TM
open VerifierVerdictAnd (one empty)
open VerifierPairRestore (word word_parked)
open VerifierAccumulate (markerDir)

def machine : TM 2 where
  Q := Fin 3
  qstart := 0
  qhalt := 2
  δ := fun q i w o =>
    if q = 0 then
      (1,fun j => readBackWrite (w j),readBackWrite o,idleDir i,
        fun j => if j = 0 then markerDir (w j) .left else idleDir (w j),idleDir o)
    else
      (2,fun j => if j = 0 then .blank else readBackWrite (w j),
        readBackWrite (Γ.ofBool (decide (w 0 = .one) && decide (w 1 ≠ .blank))),
        idleDir i,fun j => idleDir (w j),.right)
  δ_right_of_start := by
    intro q i w o
    by_cases hq : q = 0
    · simp only [hq,↓reduceIte]
      refine ⟨idleDir_right_of_start,?_,idleDir_right_of_start⟩
      intro j hj
      by_cases h : j = 0
      · subst j; simp [markerDir,hj]
      · simp [h,hj,idleDir]
    · simp only [hq,↓reduceIte]
      exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,fun _ => True.intro⟩

theorem word_present (raw : List Bool) :
    decide ((word raw).read ≠ Γ.blank) = !raw.isEmpty := by
  cases raw with
  | nil => rfl
  | cons b bs => cases b <;> rfl

theorem run (inp out : Tape) (hi : inp.read ≠ .start) (ho : out.read ≠ .start)
    (v : Bool) (raw : List Bool) :
    machine.reachesIn 2 ⟨(0 : Fin 3),inp,![one .start v,word raw],out⟩
      ⟨(2 : Fin 3),inp,![empty .start,word raw],
        out.writeAndMove (Γ.ofBool (v && !raw.isEmpty)) .right⟩ := by
  let mid : Cfg 2 (Fin 3) := ⟨1,inp,![{one .start v with head := 1},word raw],out⟩
  have h1 : machine.step ⟨(0 : Fin 3),inp,![one .start v,word raw],out⟩ = some mid := by
    simp only [TM.step,machine,show (0 : Fin 3) ≠ 2 by decide,↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · exact transitionInput_eq_self hi
    · funext j; fin_cases j
      · change (one .start v).writeAndMove .blank .left = {one .start v with head := 1}
        apply Tape.ext
        · rfl
        · funext k
          by_cases h : k = 2 <;>
            simp [Tape.writeAndMove,Tape.write,Tape.move,one,h,Function.update]
      · exact transitionTape_eq_self (word_parked raw).read_ne_start
    · exact transitionTape_eq_self ho
  have h2 : machine.step mid = some
      ⟨(2 : Fin 3),inp,![empty .start,word raw],
        out.writeAndMove (Γ.ofBool (v && !raw.isEmpty)) .right⟩ := by
    simp only [TM.step,machine,mid,show (1 : Fin 3) ≠ 2 by decide,
      show (1 : Fin 3) ≠ 0 by decide,↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · exact transitionInput_eq_self hi
    · funext j; fin_cases j
      · cases v <;> exact VerifierVerdictAnd.clear_one _ _
      · exact transitionTape_eq_self (word_parked raw).read_ne_start
    · have hv : decide (({one Γ.start v with head := 1} : Tape).read = Γ.one) = v := by
        cases v <;> rfl
      change out.writeAndMove (readBackWrite (Γ.ofBool
        (decide (({one Γ.start v with head := 1} : Tape).read = Γ.one) &&
        decide ((word raw).read ≠ Γ.blank)))) .right = _
      rw [hv,word_present]
      cases v <;> cases raw.isEmpty <;> rfl
  exact .step h1 (.step h2 .zero)

theorem emit_hoare (inp : Tape) (hi : Parked inp) (v : Bool) (raw ys : List Bool) :
    machine.HoareTime
      (fun i w o => i = inp ∧ OutAcc [v] (w 0) ∧ w 1 = word raw ∧ OutAcc ys o)
      (EmitPred inp ![word [],word raw] (ys ++ [v && !raw.isEmpty])) 2 := by
  rintro i w o ⟨hin,hv,hr,ho⟩
  subst i
  have hb : w 0 = one Γ.start v := by
    have hp : (w 0).HasBinaryPrefix [v] :=
      ⟨hv.1,hv.2.2.1,fun j hj => hv.2.2.2 (j+1) (by simp at hj; simp; omega)⟩
    rw [VerifierVerdictAnd.prefix_eq _ _ hp,hv.2.1]
  have hw : w = ![one Γ.start v,word raw] := by
    funext j; fin_cases j <;> simp [hb,hr]
  subst w
  refine ⟨_,2,le_rfl,run inp o hi.read_ne_start ho.parked.read_ne_start v raw,
    rfl,rfl,?_,outAcc_append_bit ho _⟩
  funext j; fin_cases j <;> rfl

end UnconstrainedPACDetection.FormulaClauseGuard

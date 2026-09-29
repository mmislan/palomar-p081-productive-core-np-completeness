module

public import proofs.UnconstrainedPACDetection.FormulaPairExecution

@[expose] public section

namespace UnconstrainedPACDetection.FormulaNegativeGate
open Complexity Complexity.TM DirectedLinkageSource
open FormulaCoefficientPlan (choose tag index)

/-- Consume a Boolean verdict; false enters the continuation and true skips. -/
def gate {n : Nat} (M : TM n) : TM n where
  Q := Fin 2 ⊕ M.Q
  qstart := .inl 0
  qhalt := .inr M.qhalt
  δ := fun q i w o => match q with
    | .inl k => if k = 0 then
        (.inl 1,fun j => readBackWrite (w j),readBackWrite o,idleDir i,
          fun j => idleDir (w j),moveLeftDir o)
      else
        (.inr (if o = .zero then M.qstart else M.qhalt),
          fun j => readBackWrite (w j),.blank,idleDir i,
          fun j => idleDir (w j),idleDir o)
    | .inr k =>
      let (q',wr,ow,di,dw,dout) := M.δ k i w o
      (.inr q',wr,ow,di,dw,dout)
  δ_right_of_start := by
    intro q i w o
    cases q with
    | inl k =>
      by_cases hk : k = 0
      · simp only [hk,↓reduceIte]
        exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,moveLeftDir_right_of_start⟩
      · simp only [hk,↓reduceIte]
        exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
    | inr k => exact M.δ_right_of_start k i w o

def wrap {n : Nat} (M : TM n) (c : Cfg n M.Q) : Cfg n (gate M).Q :=
  ⟨.inr c.state,c.input,c.work,c.output⟩

theorem step_lift {n : Nat} (M : TM n) {c d : Cfg n M.Q} (h : M.step c = some d) :
    (gate M).step (wrap M c) = some (wrap M d) := by
  have hn := state_ne_qhalt_of_step h
  simp only [TM.step,hn,↓reduceIte,Option.some.injEq] at h
  subst d
  simp [TM.step,gate,wrap,hn]

theorem run_lift {n : Nat} (M : TM n) {t : Nat} {c d : Cfg n M.Q}
    (h : M.reachesIn t c d) : (gate M).reachesIn t (wrap M c) (wrap M d) := by
  induction h with
  | zero => exact .zero
  | step hs _ ih => exact .step (step_lift M hs) ih

theorem inspect_run {n : Nat} (M : TM n) (v : Bool) (inp : Tape) (w : Fin n → Tape)
    (ys : List Bool) (out : Tape) (hi : Parked inp) (hw : ∀ j, Parked (w j))
    (ho : OutAcc (ys ++ [v]) out) :
    ∃ cleared, (gate M).reachesIn 2 ⟨.inl 0,inp,w,out⟩
      ⟨.inr (if v then M.qhalt else M.qstart),inp,w,cleared⟩ ∧ OutAcc ys cleared := by
  have hh : out.head = ys.length+2 := by simpa using ho.head_eq
  let prev := out.move .left
  have hp : prev.head = ys.length+1 := by simp [prev,Tape.move,hh]
  have hr : prev.read = Γ.ofBool v := by
    change out.cells prev.head = _
    rw [hp]
    simpa using ho.2.2.1 ys.length (by simp)
  let cleared := prev.writeAndMove .blank (idleDir prev.read)
  have hn : prev.read ≠ .start := by rw [hr]; cases v <;> decide
  have hclear : cleared = ⟨ys.length+1,Function.update out.cells (ys.length+1) Γ.blank⟩ := by
    change prev.writeAndMove Γ.blank (idleDir prev.read) = _
    rw [show idleDir prev.read = .stay by simp [idleDir,hn]]
    change prev.write Γ.blank = _
    simp only [Tape.write,hp,show ys.length+1 ≠ 0 by omega,↓reduceIte]
    rfl
  have hs1 : (gate M).step ⟨.inl 0,inp,w,out⟩ = some ⟨.inl 1,inp,w,prev⟩ := by
    simp only [TM.step,gate,reduceCtorEq,↓reduceIte]
    congr 1
    apply Cfg.ext
    · rfl
    · exact transitionInput_eq_self hi.read_ne_start
    · funext j; exact (hw j).writeAndMove_readBack_idle
    · rw [writeAndMove_readBack _ ho.parked.read_ne_start]
      simp [moveLeftDir,ho.read_blank,prev]
  have hs2 : (gate M).step ⟨.inl 1,inp,w,prev⟩ =
      some ⟨.inr (if v then M.qhalt else M.qstart),inp,w,cleared⟩ := by
    simp only [TM.step,gate,reduceCtorEq,show (1 : Fin 2) ≠ 0 by decide,↓reduceIte]
    congr 1
    apply Cfg.ext
    · rw [hr]; cases v <;> rfl
    · exact transitionInput_eq_self hi.read_ne_start
    · funext j; exact (hw j).writeAndMove_readBack_idle
    · rfl
  refine ⟨cleared,.step hs1 (.step hs2 .zero),?_⟩
  rw [hclear]
  refine ⟨rfl,?_,?_,?_⟩
  · simpa using ho.2.1
  · intro j hj
    change Function.update out.cells (ys.length+1) Γ.blank (j+1) = _
    rw [Function.update_of_ne (by omega)]
    have ht := ho.2.2.1 j (by simp; omega)
    have he : (ys ++ [v])[j]'(by simp; omega) = ys[j] := List.getElem_append_left hj
    exact ht.trans (congrArg Γ.ofBool he)
  · intro j hj
    change Function.update out.cells (ys.length+1) Γ.blank j = _
    by_cases he : j = ys.length+1
    · subst j; simp
    · rw [Function.update_of_ne he]
      exact ho.2.2.2 j (by simp; omega)

theorem gate_hoare {n : Nat} (M : TM n) (v : Bool) (inp : Tape) (w : Fin n → Tape)
    (ys zs : List Bool) (B : Nat) (hi : Parked inp) (hw : ∀ j, Parked (w j))
    (hb : M.HoareTime (EmitPred inp w ys) (EmitPred inp w (ys ++ zs)) B) :
    (gate M).HoareTime (EmitPred inp w (ys ++ [v]))
      (EmitPred inp w (ys ++ (if v then [] else zs))) (B+2) := by
  rintro i work out ⟨hin,hwork,ho⟩
  subst i
  subst work
  obtain ⟨cleared,hs,hc⟩ := inspect_run M v inp w ys out hi hw ho
  cases v with
  | true => exact ⟨_,2,by omega,hs,rfl,rfl,rfl,by simpa using hc⟩
  | false =>
    obtain ⟨d,t,ht,hd,hh,hdi,hdw,hdo⟩ := hb inp w cleared ⟨rfl,rfl,hc⟩
    refine ⟨wrap M d,2+t,by omega,reachesIn_trans _ hs (run_lift M hd),?_,hdi,hdw,hdo⟩
    change Sum.inr d.state = (Sum.inr M.qhalt : (gate M).Q)
    exact congrArg Sum.inr hh

end UnconstrainedPACDetection.FormulaNegativeGate

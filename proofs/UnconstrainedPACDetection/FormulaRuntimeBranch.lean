module

public import proofs.UnconstrainedPACDetection.FormulaNegativeGate

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRuntimeBranch
open Complexity Complexity.TM

/-- Copy a live finite-control bit to the output gate without changing its tape. -/
def sample {n : Nat} (slot : Fin n) : TM n where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w _ => (true,fun j => readBackWrite (w j),readBackWrite (Γ.ofBool (decide (w slot = .one))),
    idleDir i,fun j => idleDir (w j),.right)
  δ_right_of_start := by
    intro _ _ _ _
    exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,fun _ => rfl⟩

theorem sample_hoare {n : Nat} (slot : Fin n) (bit : Bool) (inp : Tape)
    (w : Fin n → Tape) (ys : List Bool) (hi : Parked inp) (hp : ∀ j, Parked (w j))
    (hb : (w slot).read = Γ.ofBool bit) : (sample slot).HoareTime
    (EmitPred inp w ys) (EmitPred inp w (ys ++ [bit])) 1 := by
  rintro i work out ⟨hin,hw,ho⟩
  subst i; subst work
  refine ⟨⟨true,inp,w,out.writeAndMove (Γ.ofBool bit) .right⟩,1,by omega,
    .step ?_ .zero,rfl,rfl,rfl,outAcc_append_bit ho bit⟩
  simp only [TM.step,sample,Bool.false_eq_true,↓reduceIte]
  congr 1
  apply Cfg.ext
  · rfl
  · exact transitionInput_eq_self hi.read_ne_start
  · funext j; exact (hp j).writeAndMove_readBack_idle
  · simp only [hb]; cases bit <;> rfl

theorem positive_skip {n : Nat} (M : TM n) (inp : Tape) (w : Fin n → Tape)
    (ys : List Bool) (hi : Parked inp) (hp : ∀ j, Parked (w j)) :
    (FormulaCoefficientGate.gate M).HoareTime (EmitPred inp w (ys ++ [false]))
      (EmitPred inp w ys) 2 := by
  rintro i work out ⟨hin,hw,ho⟩
  subst i; subst work
  obtain ⟨cleared,hs,hc⟩ := FormulaCoefficientGate.inspect_run M false inp w ys out hi hp ho
  exact ⟨_,2,by omega,hs,rfl,rfl,rfl,hc⟩

theorem negative_skip {n : Nat} (M : TM n) (inp : Tape) (w : Fin n → Tape)
    (ys : List Bool) (hi : Parked inp) (hp : ∀ j, Parked (w j)) :
    (FormulaNegativeGate.gate M).HoareTime (EmitPred inp w (ys ++ [true]))
      (EmitPred inp w ys) 2 := by
  rintro i work out ⟨hin,hw,ho⟩
  subst i; subst work
  obtain ⟨cleared,hs,hc⟩ := FormulaNegativeGate.inspect_run M true inp w ys out hi hp ho
  exact ⟨_,2,by omega,hs,rfl,rfl,rfl,hc⟩

def machine {n : Nat} (slot : Fin n) (yes no : TM n) : TM n :=
  seqTM (seqTM (sample slot) (FormulaCoefficientGate.gate yes))
    (seqTM (sample slot) (FormulaNegativeGate.gate no))

/-- Only the selected branch needs a valid entry contract. The other branch is
    physically skipped, even if its scratch layout is incompatible with this frame. -/
theorem branch_hoare {n : Nat} (slot : Fin n) (yes no : TM n) (bit : Bool)
    (inp : Tape) (w : Fin n → Tape) (zs : List Bool) (B : Nat)
    (hi : Parked inp) (hp : ∀ j, Parked (w j)) (hb : (w slot).read = Γ.ofBool bit)
    (selected : ∀ ys, (if bit then yes else no).HoareTime
      (EmitPred inp w ys) (EmitPred inp w (ys ++ zs)) B) (ys : List Bool) :
    (machine slot yes no).HoareTime (EmitPred inp w ys) (EmitPred inp w (ys ++ zs)) (B+9) := by
  cases bit with
  | true =>
    have hy := FormulaCoefficientGate.gate_hoare yes true inp w ys zs B hi hp (selected ys)
    simp only [ite_true] at hy
    have h₁ := seqTM_hoareTime _ _ (sample_hoare slot true inp w ys hi hp hb)
      (emitPred_transition hi hp _) hy
    have h₂ := seqTM_hoareTime _ _ (sample_hoare slot true inp w (ys ++ zs) hi hp hb)
      (emitPred_transition hi hp _) (negative_skip no inp w (ys ++ zs) hi hp)
    have h := seqTM_hoareTime _ _ h₁ (emitPred_transition hi hp _) h₂
    exact h.mono_bound (by omega)
  | false =>
    have h₁ := seqTM_hoareTime _ _ (sample_hoare slot false inp w ys hi hp hb)
      (emitPred_transition hi hp _) (positive_skip yes inp w ys hi hp)
    have hn := FormulaNegativeGate.gate_hoare no false inp w ys zs B hi hp (selected ys)
    simp only [Bool.false_eq_true,ite_false] at hn
    have h₂ := seqTM_hoareTime _ _ (sample_hoare slot false inp w ys hi hp hb)
      (emitPred_transition hi hp _) hn
    have h := seqTM_hoareTime _ _ h₁ (emitPred_transition hi hp _) h₂
    exact h.mono_bound (by omega)

end UnconstrainedPACDetection.FormulaRuntimeBranch

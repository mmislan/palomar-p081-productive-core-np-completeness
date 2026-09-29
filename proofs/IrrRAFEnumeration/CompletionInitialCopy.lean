module

public import proofs.IrrRAFEnumeration.CompletionInitialBase

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def copyParkedBufferTM {n : Nat} (src dst : Fin n) : TM n :=
  seqTM (copyWorkToWorkTM src dst) (seqTM (rewindWorkTM src) (rewindWorkTM dst))

/-- Exact copy and both rewinds; the destination is the only lasting change. -/
theorem copyParkedBuffer_correct {n : Nat} (src dst : Fin n) (hne : src ≠ dst)
    (xs : List Bool) (inp : Tape) (work : Fin n → Tape)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hs : work src = parkedInput xs) (hd : work dst = regTape 0) :
    (copyParkedBufferTM src dst).HoareTime (EmitPred inp work [])
      (EmitPred inp (Function.update work dst (parkedInput xs)) []) (3*xs.length+9) := by
  let A := accumulatorTape xs
  let W := Function.update (Function.update work src A) dst A
  let W₁ := Function.update work dst A
  let W₂ := Function.update work dst (parkedInput xs)
  have hpA : Parked A := (accumulatorTape_outAcc xs).parked
  have hpW : ∀ i, Parked (W i) := by
    intro i
    by_cases hd : i = dst
    · subst i; simpa [W] using hpA
    · by_cases hs : i = src
      · subst i; simpa [W,Function.update_of_ne hne] using hpA
      · simpa [W,Function.update_of_ne hd,Function.update_of_ne hs] using hw i
  have hpW₁ : ∀ i, Parked (W₁ i) := by
    intro i
    by_cases hi : i = dst
    · subst i; simpa [W₁] using hpA
    · simpa [W₁,Function.update_of_ne hi] using hw i
  have hpW₂ : ∀ i, Parked (W₂ i) := by
    intro i
    by_cases hi : i = dst
    · subst i; simpa [W₂] using parkedInput_parked xs
    · simpa [W₂,Function.update_of_ne hi] using hw i
  let P : TM.TapePred n := fun a w out => a = inp ∧
    (∀ i, i ≠ src → i ≠ dst → w i = work i) ∧ OutAcc [] out
  have hc := copyWorkToWorkTM_hoareTime_frame_of_hasOutput src dst hne xs
    (parkedInput xs) (P := P) (by
      rintro a w out a' w' out' ⟨ha,hw,ho⟩ _ _ _ _ _ hi hout hother
      exact ⟨hi.trans ha,fun i his hid => (hother i his hid).trans (hw i his hid),
        hout.symm ▸ ho⟩)
  have hcopy : (copyWorkToWorkTM src dst).HoareTime (EmitPred inp work [])
      (EmitPred inp W []) (xs.length+1) := by
    apply hc.consequence
    · rintro a w out ⟨ha,hww,ho⟩
      subst a; subst w
      refine ⟨hs,rfl,?_,?_,hp.read_ne_start,ho.parked.read_ne_start,ho.parked.1,
        fun i _ _ => ⟨(hw i).read_ne_start,(hw i).1⟩,rfl,fun _ _ _ => rfl,ho⟩
      · exact (accumulatorTape_outAcc xs).hasOutput
      · rw [hd]
        exact (reg_zero_init_bumped.eq_regT).symm
    · rintro a w out ⟨hcs,hhs,_,hpd,hzero,ha,hother,ho⟩
      refine ⟨ha,?_,ho⟩
      funext i
      by_cases hid : i = dst
      · subst i
        simp only [W,Function.update_self]
        apply Tape.ext
        · simpa [A,accumulatorTape,advanceInput,parkedInput,Nat.add_comm] using hpd.1
        · exact hpd.cells_eq_init hzero
      · by_cases his : i = src
        · subst i
          simp only [W,Function.update_of_ne hne,Function.update_self]
          apply Tape.ext
          · simpa [A,accumulatorTape,advanceInput,parkedInput,Nat.add_comm] using hhs
          · exact hcs
        · simpa [W,Function.update_of_ne hid,Function.update_of_ne his] using hother i his hid
    · rfl
  have hr₁ := rewindBuffer_correct src inp W₁ [] xs.length hp hpW₁
    (by simp [W₁,Function.update_of_ne hne,hs,parkedInput])
    (by simp [W₁,Function.update_of_ne hne,hs,parkedInput,Tape.init])
  have he₁ : Function.update W₁ src (advanceInput (W₁ src) xs.length) = W := by
    funext i
    by_cases his : i = src
    · subst i; simp [W₁,W,Function.update_of_ne hne,hs,A,accumulatorTape]
    · by_cases hid : i = dst
      · subst i; simp [W₁,W,Function.update_of_ne (Ne.symm hne)]
      · simp [W₁,W,Function.update_of_ne his,Function.update_of_ne hid]
  rw [he₁] at hr₁
  have hr₂ := rewindBuffer_correct dst inp W₂ [] xs.length hp hpW₂
    (by simp [W₂,parkedInput]) (by simp [W₂,parkedInput,Tape.init])
  have he₂ : Function.update W₂ dst (advanceInput (W₂ dst) xs.length) = W₁ := by
    simp [W₂,W₁,A,accumulatorTape]
  rw [he₂] at hr₂
  have htail := seqTM_hoareTime _ _ hr₁ (emitPred_transition hp hpW₁ []) hr₂
  have h := seqTM_hoareTime _ _ hcopy (emitPred_transition hp hpW []) htail
  exact h.mono_bound (by omega)

end IrrRAFEnumeration.CompletionQuery

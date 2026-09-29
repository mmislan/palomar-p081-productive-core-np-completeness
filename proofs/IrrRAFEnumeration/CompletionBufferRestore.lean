module

public import proofs.IrrRAFEnumeration.CompletionVirtualEmitter

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

theorem rewindBuffer_correct {k : Nat} (src : Fin k) (inp : Tape)
    (work : Fin k → Tape) (ys : List Bool) (n : Nat)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hh : (work src).head = 1) (hs : (work src).cells 0 = Γ.start) :
    (rewindWorkTM src).HoareTime
      (EmitPred inp (Function.update work src (advanceInput (work src) n)) ys)
      (EmitPred inp work ys) (n+3) := by
  let P : TM.TapePred k := fun a w out => a = inp ∧ (w src).cells = (work src).cells ∧
    (∀ i, i ≠ src → w i = work i) ∧ OutAcc ys out
  have h := rewindWorkTM_hoareTime_frame src (n+1) (P := P) (by
    rintro a w out a' w' out' ⟨ha,hc,hww,ho⟩ hcells _ hother hin houtc houth
    refine ⟨hin.trans ha,hcells.trans hc,fun i hi => (hother i hi).trans (hww i hi),?_⟩
    have he : out' = out := Tape.ext houth houtc
    exact he.symm ▸ ho)
  apply h.consequence
  · rintro a w out ⟨ha,hww,ho⟩
    subst a
    subst w
    refine ⟨?_,?_,?_,hp.read_ne_start,ho.parked.read_ne_start,ho.parked.1,?_,rfl,?_,?_,ho⟩
    · simpa [advanceInput] using hs
    · simpa [advanceInput] using (hw src).2
    · simp [advanceInput,hh,Nat.add_comm]
    · intro i hi
      simpa [Function.update_of_ne hi] using ⟨(hw i).read_ne_start,(hw i).1⟩
    · simp [advanceInput]
    · intro i hi
      simp [Function.update_of_ne hi]
  · rintro a w out ⟨hhead,ha,hcells,hother,ho⟩
    refine ⟨ha,?_,ho⟩
    funext i
    by_cases hi : i = src
    · subst i
      exact Tape.ext (hhead.trans hh.symm) hcells
    · exact hother i hi
  · omega

def appendRestoreTM {k : Nat} (src : Fin k) : TM k :=
  seqTM (appendBufferTM src) (rewindWorkTM src)

/-- Appending a stored buffer restores its read head for the next query. -/
theorem appendRestoreTM_correct {k : Nat} (src : Fin k) (xs : List Bool)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hh : (work src).head = 1) (hs : (work src).cells 0 = Γ.start)
    (hx : BufferChunk xs (work src)) :
    (appendRestoreTM src).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys++xs)) (2*xs.length+5) := by
  have h₁ := appendBufferTM_correct src xs inp work ys hp hw hx
  have h₂ := rewindBuffer_correct src inp work (ys++xs) xs.length hp hw hh hs
  have hwp : ∀ i, Parked (Function.update work src (advanceInput (work src) xs.length) i) := by
    intro i
    by_cases hi : i = src
    · subst i
      simpa using advanceInput_parked (work src) xs.length (hw src)
    · simpa [Function.update_of_ne hi] using hw i
  have h := seqTM_hoareTime _ _ h₁ (emitPred_transition hp hwp _) h₂
  exact h.mono_bound (by omega)

theorem parkedInput_chunk (xs : List Bool) : BufferChunk xs (parkedInput xs) := by
  constructor
  · intro i hi
    change (Tape.init (xs.map Γ.ofBool)).cells (1+i) = _
    simpa [Nat.add_comm] using Tape.init_ofBool_cells_lt xs i hi
  · change (Tape.init (xs.map Γ.ofBool)).cells (1+xs.length) = Γ.blank
    simpa [Nat.add_comm] using Tape.init_ofBool_cells_ge xs xs.length le_rfl

end IrrRAFEnumeration.CompletionQuery

module

public import proofs.IrrRAFEnumeration.CompletionBaseCompiler

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

/-- Append a blank-terminated work buffer, preserving its cells and every other tape. -/
def appendBufferTM {k : Nat} (src : Fin k) : TM k where
  Q := Bool
  qstart := false
  qhalt := true
  δ := fun _ i w o =>
    if w src = Γ.blank then
      (true,fun j => readBackWrite (w j),readBackWrite o,
        idleDir i,fun j => idleDir (w j),idleDir o)
    else
      (false,fun j => readBackWrite (w j),readBackWrite (w src),
        idleDir i,fun j => if j = src then Dir3.right else idleDir (w j),Dir3.right)
  δ_right_of_start := by
    intro q i w o
    dsimp only
    by_cases hblank : w src = Γ.blank
    · simp only [hblank,ite_true]
      exact ⟨idleDir_right_of_start,fun _ => idleDir_right_of_start,idleDir_right_of_start⟩
    · simp only [hblank,ite_false]
      refine ⟨idleDir_right_of_start,?_,fun _ => True.intro⟩
      intro j hj
      by_cases h : j = src
      · simp [h]
      · simpa [h] using idleDir_right_of_start hj

def BufferChunk (xs : List Bool) (source : Tape) : Prop :=
  (∀ i, (hi : i < xs.length) → source.cells (source.head+i) = Γ.ofBool xs[i]) ∧
    source.cells (source.head+xs.length) = Γ.blank

theorem appendBuffer_step_bit {k : Nat} (src : Fin k) (b : Bool)
    (inp : Tape) (work : Fin k → Tape) (out : Tape)
    (hp : Parked inp) (hw : ∀ i, Parked (work i))
    (hr : (work src).read = Γ.ofBool b) :
    (appendBufferTM src).step ⟨false,inp,work,out⟩ = some
      ⟨false,inp,Function.update work src (advanceInput (work src) 1),
        out.writeAndMove (Γ.ofBool b) .right⟩ := by
  have hn : (work src).read ≠ Γ.blank := by rw [hr]; cases b <;> decide
  simp only [TM.step,appendBufferTM,Bool.false_eq_true,ite_false,ite_eq_right hn]
  apply congrArg some
  refine Cfg.ext rfl hp.move_idle ?_ ?_
  · funext j
    dsimp only
    by_cases hj : j = src
    · subst j
      rw [ite_eq_left rfl,Function.update_self,writeAndMove_readBack _ (hw src).read_ne_start]
      rfl
    · rw [ite_eq_right hj,Function.update_of_ne hj]
      exact (hw j).writeAndMove_readBack_idle
  · rw [hr]
    cases b <;> rfl

theorem appendBuffer_step_blank {k : Nat} (src : Fin k)
    (inp : Tape) (work : Fin k → Tape) (out : Tape)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) (ho : Parked out)
    (hr : (work src).read = Γ.blank) :
    (appendBufferTM src).step ⟨false,inp,work,out⟩ = some ⟨true,inp,work,out⟩ := by
  simp only [TM.step,appendBufferTM,Bool.false_eq_true,ite_false,ite_eq_left hr]
  apply congrArg some
  exact Cfg.ext rfl hp.move_idle (funext (fun j => (hw j).writeAndMove_readBack_idle))
    ho.writeAndMove_readBack_idle

theorem appendBufferTM_correct {k : Nat} (src : Fin k) (xs : List Bool)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ i, Parked (work i)) (hx : BufferChunk xs (work src)) :
    (appendBufferTM src).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work src (advanceInput (work src) xs.length)) (ys++xs))
      (xs.length+1) := by
  induction xs generalizing work ys with
  | nil =>
    rintro a w out ⟨ha,hw0,hout⟩
    subst a
    subst w
    have hr : (work src).read = Γ.blank := by simpa [BufferChunk,Tape.read] using hx.2
    have hs := appendBuffer_step_blank src inp work out hp hw hout.parked hr
    refine ⟨⟨true,inp,work,out⟩,1,le_rfl,.step hs .zero,rfl,rfl,?_,?_⟩
    · simp [advanceInput]
    · simpa using hout
  | cons b xs ih =>
    rintro a w out ⟨ha,hw0,hout⟩
    subst a
    subst w
    have hr : (work src).read = Γ.ofBool b := by
      have h := hx.1 0 (by simp)
      simpa only [Tape.read,Nat.add_zero,List.getElem_cons,dite_true] using h
    let w' := Function.update work src (advanceInput (work src) 1)
    let o' := out.writeAndMove (Γ.ofBool b) .right
    have hw' : ∀ i, Parked (w' i) := by
      intro i
      by_cases hi : i = src
      · subst i
        simpa [w'] using advanceInput_parked (work src) 1 (hw src)
      · simpa [w',Function.update_of_ne hi] using hw i
    have hx' : BufferChunk xs (w' src) := by
      constructor
      · intro i hi
        have h := hx.1 (i+1) (by simpa using hi)
        simpa [w',advanceInput,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
      · simpa [w',advanceInput,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hx.2
    have ho' : OutAcc (ys++[b]) o' := outAcc_append_bit hout b
    obtain ⟨c,t,ht,hreach,hh,hi,hwork,ho⟩ := ih w' (ys++[b]) hw' hx' inp w' o' ⟨rfl,rfl,ho'⟩
    have hs := appendBuffer_step_bit src b inp work out hp hw hr
    have he : Function.update w' src (advanceInput (w' src) xs.length) =
        Function.update work src (advanceInput (work src) (b::xs).length) := by
      have hadvance : advanceInput (advanceInput (work src) 1) xs.length =
          advanceInput (work src) (b::xs).length := by
        apply Tape.ext
        · dsimp [advanceInput]
          omega
        · rfl
      simpa only [w',Function.update_self,Function.update_idem] using
        congrArg (Function.update work src) hadvance
    refine ⟨c,t+1,by simp only [List.length_cons]; omega,?_,hh,hi,?_,?_⟩
    · exact .step hs hreach
    · exact hwork.trans he
    · simpa [List.append_assoc] using ho

end IrrRAFEnumeration.CompletionQuery

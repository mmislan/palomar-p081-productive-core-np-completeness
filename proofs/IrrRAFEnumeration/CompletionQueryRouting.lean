module

public import proofs.IrrRAFEnumeration.CompletionSATInvocation

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

def accumulatorTape (xs : List Bool) : Tape := advanceInput (parkedInput xs) xs.length

theorem accumulatorTape_outAcc (xs : List Bool) : OutAcc xs (accumulatorTape xs) := by
  refine ⟨by simp [accumulatorTape,advanceInput,parkedInput,Nat.add_comm],rfl,?_,?_⟩
  · intro i hi
    exact Tape.init_ofBool_cells_lt xs i hi
  · intro j hj
    obtain ⟨i,rfl⟩ : ∃ i, j = i+1 := ⟨j-1,by omega⟩
    exact Tape.init_ofBool_cells_ge xs i (by omega)

/-- Redirect an exact query emitter into a work tape, retaining exact state. -/
theorem redirectEmitter_correct {n : Nat} (M : TM n)
    (inp inp' : Tape) (work work' : Fin n → Tape) (ys zs : List Bool) (b : Nat)
    (h : M.HoareTime (EmitPred inp work ys) (EmitPred inp' work' zs) b) :
    M.retargetOutput.HoareTime
      (EmitPred inp (frameWork (m := 1) work (fun _ => accumulatorTape ys)) [])
      (EmitPred inp' (frameWork (m := 1) work' (fun _ => accumulatorTape zs)) []) b := by
  rintro a w out ⟨ha,hw,ho⟩
  subst a
  subst w
  have he : out = (Tape.init []).move Dir3.right := ho.eq outAcc_nil_init
  subst out
  obtain ⟨c,t,ht,hr,hh,hi,hww,hout⟩ := h inp work (accumulatorTape ys)
    ⟨rfl,rfl,accumulatorTape_outAcc ys⟩
  have heout := hout.eq (accumulatorTape_outAcc zs)
  have hrun := retargetOutput_reachesIn_retargetCfg_frame M hr
  refine ⟨M.retargetCfg c,t,ht,hrun,hh,hi,?_,outAcc_nil_init⟩
  change (fun i : Fin (n+1) => if h : i.val < n then c.work ⟨i.val,h⟩ else c.output) = _
  rw [hww,heout]
  rfl

/-- The query's output accumulator becomes a canonical virtual input by rewinding only. -/
theorem rewindQuery_correct {n : Nat} (work : Fin n → Tape) (inp : Tape)
    (xs : List Bool) (hp : Parked inp) (hw : ∀ i, Parked (work i)) :
    (rewindWorkTM (Fin.last n)).HoareTime
      (EmitPred inp (frameWork (m := 1) work (fun _ => accumulatorTape xs)) [])
      (EmitPred inp (frameWork (m := 1) work (fun _ => parkedInput xs)) []) (xs.length+3) := by
  let W := frameWork (m := 1) work (fun _ => parkedInput xs)
  have hwp : ∀ i, Parked (W i) := by
    intro i
    unfold W frameWork
    split
    · exact hw _
    · exact parkedInput_parked _
  have h := rewindBuffer_correct (Fin.last n) inp W [] xs.length hp hwp
    (by simp [W,frameWork,parkedInput]) (by simp [W,frameWork,parkedInput,Tape.init])
  have he : Function.update W (Fin.last n) (advanceInput (W (Fin.last n)) xs.length) =
      frameWork (m := 1) work (fun _ => accumulatorTape xs) := by
    funext i
    by_cases hi : i.val < n
    · have hn : i ≠ Fin.last n := by intro he; have := congrArg Fin.val he; simp at this; omega
      simp [W,frameWork,Function.update_of_ne hn,hi]
    · have he : i = Fin.last n := Fin.ext (by simp; omega)
      subst i
      simp [W,frameWork,accumulatorTape]
  rw [he] at h
  exact h

end IrrRAFEnumeration.CompletionQuery

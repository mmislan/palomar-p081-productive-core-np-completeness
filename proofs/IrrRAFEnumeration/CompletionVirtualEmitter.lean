module

public import proofs.IrrRAFEnumeration.CompletionBufferAppend
public import proofs.Complexitylib.Models.TuringMachine.Combinators.Internal.Retarget

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

theorem virtualInput_step_preserves_real {k : Nat} (M : TM k)
    {c c' : Cfg (k+1) (retargetInput M).Q}
    (hs : (retargetInput M).step c = some c') (hp : Parked c.input) :
    c'.input = c.input := by
  simp only [TM.step] at hs
  split at hs
  · contradiction
  · cases hs
    exact hp.move_idle

theorem virtualInput_run_preserves_real {k : Nat} (M : TM k)
    {c c' : Cfg (k+1) (retargetInput M).Q} {t : Nat}
    (hr : (retargetInput M).reachesIn t c c') (hp : Parked c.input) :
    c'.input = c.input := by
  induction hr with
  | zero => rfl
  | @step a b c t hs _ ih =>
    have he := virtualInput_step_preserves_real M hs hp
    have hb : Parked b.input := he.symm ▸ hp
    exact (ih hb).trans he

/-- Run an existing emitter on a work-buffer input, preserving the real CRS tape. -/
theorem virtualEmitter_correct {k : Nat} (M : TM k)
    (real vin vin' : Tape) (work work' : Fin k → Tape) (ys zs : List Bool) (b : Nat)
    (hp : Parked real) (hv : vin.StartInvariant) (hw : ∀ i, (work i).StartInvariant)
    (hM : M.HoareTime (EmitPred vin work ys) (EmitPred vin' work' zs) b) :
    (retargetInput M).HoareTime
      (EmitPred real (frameWork (m := 1) work (fun _ => vin)) ys)
      (EmitPred real (frameWork (m := 1) work' (fun _ => vin')) zs) b := by
  rintro a w out ⟨ha,hww,hout⟩
  subst a
  subst w
  obtain ⟨c,t,ht,hr,hh,hi,hwork,ho⟩ := hM vin work out ⟨rfl,rfl,hout⟩
  have hoStart : out.StartInvariant := ⟨hout.2.1,hout.parked.2⟩
  obtain ⟨real',hvr⟩ := retargetInput_reachesIn_of_reachesIn M hr hv hw hoStart real
  have he : real' = real := virtualInput_run_preserves_real M hvr hp
  subst real'
  refine ⟨retargetWrap M real c,t,ht,hvr,hh,rfl,?_,ho⟩
  change (fun i : Fin (k+1) => if h : i.val < k then c.work ⟨i.val,h⟩ else c.input) = _
  rw [hwork,hi]
  rfl

end IrrRAFEnumeration.CompletionQuery

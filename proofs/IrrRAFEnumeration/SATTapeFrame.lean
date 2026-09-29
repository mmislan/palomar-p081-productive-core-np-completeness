module

public import proofs.Complexitylib.Models.TuringMachine.Registers.Emit
public import proofs.Complexitylib.Models.TuringMachine.Lift

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def frameWork {n m : Nat} (work : Fin n → Tape) (extra : Fin (n+m) → Tape) :
    Fin (n+m) → Tape := fun i => if h : i.val < n then work ⟨i.val,h⟩ else extra i

def frameCfg {n : Nat} (tm : TM n) (m : Nat) (extra : Fin (n+m) → Tape)
    (c : Cfg n tm.Q) : Cfg (n+m) tm.Q :=
  {state := c.state, input := c.input, work := frameWork c.work extra, output := c.output}

theorem liftTM_step_frame {n : Nat} (tm : TM n) (m : Nat)
    (extra : Fin (n+m) → Tape) (he : ∀ i, n ≤ i.val → Parked (extra i))
    (c : Cfg n tm.Q) :
    (tm.liftTM m).step (frameCfg tm m extra c) =
      (tm.step c).map (frameCfg tm m extra) := by
  have hinner : (fun i : Fin n => ((frameWork c.work extra) (Fin.castAdd m i)).read) =
      fun i => (c.work i).read := by
    funext i
    simp only [frameWork, Fin.val_castAdd, dite_eq_left i.isLt]
  by_cases hh : c.state = tm.qhalt
  · simp only [TM.step, frameCfg, liftTM, hh, ↓reduceIte, Option.map_none]
  · simp only [TM.step, frameCfg, liftTM, hh, ↓reduceIte, Option.map_some]
    rw [hinner]
    refine congrArg some ((Cfg.mk.injEq ..).mpr ⟨rfl,rfl,?_,rfl⟩)
    funext i
    by_cases hi : i.val < n
    · simp only [frameWork, dite_eq_left hi]
    · simp only [frameWork, dite_eq_right hi]
      exact (he i (by omega)).writeAndMove_readBack_idle

theorem liftTM_reaches_frame {n : Nat} (tm : TM n) (m : Nat)
    (extra : Fin (n+m) → Tape) (he : ∀ i, n ≤ i.val → Parked (extra i))
    {t : Nat} {c c' : Cfg n tm.Q} (h : tm.reachesIn t c c') :
    (tm.liftTM m).reachesIn t (frameCfg tm m extra c) (frameCfg tm m extra c') := by
  induction h with
  | zero => exact .zero
  | step hs _ ih => exact .step (by rw [liftTM_step_frame tm m extra he, hs]; rfl) ih

/-- Lift an emitter into an occupied outer register layout with exactly the
same time bound. Only the unused extra tapes must be parked. -/
theorem liftTM_frame_correct {n : Nat} (tm : TM n) (m : Nat)
    (extra : Fin (n+m) → Tape) (he : ∀ i, n ≤ i.val → Parked (extra i))
    (inp inp' : Tape) (work work' : Fin n → Tape) (ys zs : List Bool) (b : Nat)
    (h : tm.HoareTime (EmitPred inp work ys) (EmitPred inp' work' zs) b) :
    (tm.liftTM m).HoareTime (EmitPred inp (frameWork work extra) ys)
      (EmitPred inp' (frameWork work' extra) zs) b := by
  rintro input w out ⟨hi,hw,hout⟩
  subst input
  subst w
  obtain ⟨c,t,ht,hr,hh,hi,hw,ho⟩ := h inp work out ⟨rfl,rfl,hout⟩
  refine ⟨frameCfg tm m extra c,t,ht,liftTM_reaches_frame tm m extra he hr,hh,hi,?_,ho⟩
  change frameWork c.work extra = frameWork work' extra
  rw [hw]

end IrrRAFEnumeration.SATSource

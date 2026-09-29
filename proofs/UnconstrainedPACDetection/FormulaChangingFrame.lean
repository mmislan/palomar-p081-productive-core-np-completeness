module

public import proofs.UnconstrainedPACDetection.FormulaRoutedFrame

@[expose] public section

namespace UnconstrainedPACDetection.FormulaChangingFrame
open Complexity Complexity.TM

/-- Placement transports a changing subroutine frame and retains the exact outside tapes. -/
theorem hoare {n : Nat} (M : TM n) (pre post : Nat) (inp : Tape)
    (small result : Fin n → Tape) (large final : Fin (pre+n+post) → Tape)
    (ys zs : List Bool) (B : Nat) (hp : ∀ j, Parked (large j))
    (hm : ∀ j, large (placeWorkIdx pre post j) = small j)
    (hf : ∀ j, final (placeWorkIdx pre post j) = result j)
    (hout : ∀ j, ¬placeWorkInMiddle pre n j → large j = final j)
    (h : M.HoareTime (EmitPred inp small ys) (EmitPred inp result zs) B) :
    (placeWorkTM pre post M).HoareTime (EmitPred inp large ys) (EmitPred inp final zs) B := by
  rintro i w out ⟨hi,hw,ho⟩
  subst i; subst w
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := h _ _ out ⟨rfl,rfl,ho⟩
  have he (c : Cfg n M.Q) (hc : c.work = small) :
      (placeWorkCfg M pre post large c).work = large := by
    funext j
    simp only [placeWorkCfg]
    split
    next hj => rw [hc,← hm,placeWorkIdx_placeWorkCoord]
    next => rfl
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal M pre post large hr
    (by intro j _; exact (hp j).read_ne_start)
  refine ⟨placeWorkCfg M pre post large d,t,ht,?_,hh,hdi,?_,hdo⟩
  · convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · exact (he _ rfl).symm
    · rfl
  · funext j
    simp only [placeWorkCfg]
    split
    next hj => rw [hdw,← hf,placeWorkIdx_placeWorkCoord]
    next hj => exact hout j hj

def extend {n : Nat} (w : Fin n → Tape) (fuel : Tape) (t : Fin (0+n+1)) : Tape :=
  if h : t.val < n then w ⟨t.val,h⟩ else fuel

theorem parked {n : Nat} (w : Fin n → Tape) (fuel : Tape)
    (hp : ∀ t, Parked (w t)) (hf : Parked fuel) : ∀ t, Parked (extend w fuel t) := by
  intro t; unfold extend; split
  · exact hp _
  · exact hf

theorem append_hoare {n : Nat} (M : TM n) (inp : Tape) (w z : Fin n → Tape)
    (fuel : Tape) (ys zs : List Bool) (B : Nat) (hp : ∀ t, Parked (w t)) (hf : Parked fuel)
    (h : M.HoareTime (EmitPred inp w ys) (EmitPred inp z zs) B) :
    (placeWorkTM 0 1 M).HoareTime (EmitPred inp (extend w fuel) ys)
      (EmitPred inp (extend z fuel) zs) B := by
  apply hoare M 0 1 inp w z _ _ ys zs B (parked w fuel hp hf) _ _ _ h
  · intro j; simp [extend,placeWorkIdx,j.isLt]
  · intro j; simp [extend,placeWorkIdx,j.isLt]
  · intro j hj
    have hn : ¬j.val < n := by simpa [placeWorkInMiddle] using hj
    simp [extend,hn]

end UnconstrainedPACDetection.FormulaChangingFrame

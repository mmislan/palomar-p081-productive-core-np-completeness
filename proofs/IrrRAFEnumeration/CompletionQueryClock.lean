module

public import proofs.IrrRAFEnumeration.CompletionQueryDecision
public import proofs.IrrRAFEnumeration.PolynomialClockSetup
public import proofs.Complexitylib.Models.TuringMachine.Placement.Internal

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM PolynomialClockSetup

noncomputable def scratchBoundPolynomial (p : Polynomial Nat) : Polynomial Nat := p+Polynomial.X+2

theorem scratchBound_eval (p : Polynomial Nat) (L : Nat) :
    (scratchBoundPolynomial p).eval L = p.eval L+L+2 := by
  simp [scratchBoundPolynomial]

/-- Measure the already-formed query and evaluate a fixed polynomial in unary. -/
def queryClockTM (p : Polynomial Nat) : TM 3 :=
  seqTM (inputLenRegTM 0) (polyEvalTM 0 1 2 p)

theorem queryClockTM_correct (p : Polynomial Nat) (x : List Bool) :
    (queryClockTM p).HoareTime
      (EmitPred (parkedInput x) initialWork [])
      (EmitPred (parkedInput x) (clockWork p x.length) [])
      (setupTime p x.length) := by
  let q := p
  let input := parkedInput x
  have hi : Parked input := parkedInput_parked x
  have h0 : ∀ i, Parked (initialWork i) := fun _ => parked_regTape 0
  have h1 := PolynomialClockSetup.lengthWork_parked x.length
  have hcap : x.length ≤ valueCap q x.length := Nat.le_add_right _ _
  have hpre : ∀ k, k ≤ q.natDegree+1 →
      hornerFold x.length ((polyCoeffs q).take k) 0 ≤ valueCap q x.length := by
    intro k _
    have h := hornerFold_take_le x.length (polyCoeffs q) k
    rw [polyCoeffs_length] at h
    exact h.trans (Nat.le_add_left _ _)
  have hpoly := polyEvalTM_hoareTime (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
    q (valueCap q x.length) x.length 0 0 hcap (Nat.zero_le _) (Nat.zero_le _) hpre
    input (PolynomialClockSetup.lengthWork x.length) [] hi h1
    (by simp [PolynomialClockSetup.lengthWork]) (by simp [PolynomialClockSetup.lengthWork,initialWork])
    (by simp [PolynomialClockSetup.lengthWork,initialWork])
  have hlen := inputLenRegTM_hoareTime (0 : Fin 3) x initialWork []
    (fun i _ => h0 i) rfl
  have hrest := seqTM_hoareTime _ _ hlen (emitPred_transition hi h1 []) hpoly
  dsimp only [q] at hrest
  exact hrest.mono_bound (by unfold setupTime; omega)

def virtualQueryClockTM (p : Polynomial Nat) (k : Nat) : TM (3+k+1) :=
  retargetInput ((queryClockTM p).liftTM k)

/-- Actual clock execution on the query buffer, preserving original CRS input
and the k fresh solver tapes. -/
theorem virtualQueryClockTM_correct (p : Polynomial Nat) (k : Nat)
    (x : List Bool) (inp : Tape) (hp : Parked inp) :
    (virtualQueryClockTM p k).HoareTime
      (EmitPred inp (frameWork (m := 1)
        (frameWork (m := k) initialWork (fun _ => regTape 0))
        (fun _ => parkedInput x)) [])
      (EmitPred inp (frameWork (m := 1)
        (frameWork (m := k) (clockWork p x.length)
          (fun _ => regTape 0)) (fun _ => parkedInput x)) [])
      (setupTime p x.length) := by
  have h := liftTM_frame_correct (queryClockTM p) k (fun _ => regTape 0)
    (fun _ _ => parked_regTape 0) _ _ _ _ _ _ _ (queryClockTM_correct p x)
  have hw : ∀ i, ((frameWork (m := k) initialWork (fun _ => regTape 0)) i).StartInvariant := by
    intro i
    have he : (frameWork (m := k) initialWork (fun _ => regTape 0)) i = regTape 0 := by
      simp [frameWork,initialWork]
    rw [he]
    exact ⟨regCells_zero 0,(parked_regTape 0).2⟩
  exact virtualEmitter_correct ((queryClockTM p).liftTM k) inp _ _ _ _ _ _ _ hp
    ⟨by rfl,(parkedInput_parked x).2⟩ hw h

def placedClockWork {n : Nat} (pre post : Nat)
    (extras : Fin (pre+n+post) → Tape) (work : Fin n → Tape) : Fin (pre+n+post) → Tape :=
  fun i => if h : placeWorkInMiddle pre n i then work (placeWorkCoord pre n i h) else extras i

theorem placeEmitter_correct {n : Nat} (M : TM n) (pre post : Nat)
    (extras : Fin (pre+n+post) → Tape)
    (he : ∀ i, ¬placeWorkInMiddle pre n i → Parked (extras i))
    (inp inp' : Tape) (work work' : Fin n → Tape) (ys zs : List Bool) (bound : Nat)
    (hM : M.HoareTime (EmitPred inp work ys) (EmitPred inp' work' zs) bound) :
    (placeWorkTM pre post M).HoareTime
      (EmitPred inp (placedClockWork pre post extras work) ys)
      (EmitPred inp' (placedClockWork pre post extras work') zs) bound := by
  rintro a w out ⟨ha,hw,ho⟩
  subst a
  subst w
  obtain ⟨c,t,ht,hr,hh,hi,hww,hout⟩ := hM inp work out ⟨rfl,rfl,ho⟩
  have hrun := placeWorkTM_reachesIn_placeWorkCfg_stable_internal M pre post extras hr
    (fun i h => (he i h).read_ne_start)
  refine ⟨placeWorkCfg M pre post extras c,t,ht,hrun,hh,hi,?_,hout⟩
  change (fun i => if h : placeWorkInMiddle pre n i then c.work (placeWorkCoord pre n i h)
    else extras i) = _
  rw [hww]
  rfl

/-- Clock initialization in the actual seven-prefix query layout. -/
theorem placedQueryClockTM_correct (p : Polynomial Nat) (k : Nat)
    (x : List Bool) (inp : Tape) (hp : Parked inp)
    (extras : Fin (7+(3+k+1)+0) → Tape)
    (he : ∀ i, ¬placeWorkInMiddle (post := 0) 7 (3+k+1) i → Parked (extras i)) :
    (placeWorkTM 7 0 (virtualQueryClockTM p k)).HoareTime
      (EmitPred inp (placedClockWork 7 0 extras (frameWork (m := 1)
        (frameWork (m := k) initialWork (fun _ => regTape 0))
        (fun _ => parkedInput x))) [])
      (EmitPred inp (placedClockWork 7 0 extras (frameWork (m := 1)
        (frameWork (m := k) (clockWork p x.length)
          (fun _ => regTape 0)) (fun _ => parkedInput x))) [])
      (setupTime p x.length) :=
  placeEmitter_correct _ 7 0 extras he _ _ _ _ _ _ _ (virtualQueryClockTM_correct p k x inp hp)

end IrrRAFEnumeration.CompletionQuery

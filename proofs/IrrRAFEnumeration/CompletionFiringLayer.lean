module

public import proofs.IrrRAFEnumeration.CompletionFiringRow

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def firingLayerStepTM : TM 8 :=
  seqTM firingRowTM (seqTM (catalystAdvanceTM.liftTM 1) (incRegTM 7))

def firingLayerStepBudget (d r i : Nat) :=
  3*(firingBase d r i+r)+3*r+23+
    (d*(5*reactantStart d r r+5*(r+i*d)+3*(firingBase d r i+r)+10*d+63)+d+2)+1+
    (catalystAdvanceTime d (reactantStart d r r+d) (r+i*d+d) (r+i*d)
      (firingBase d r i+r)+1+(2*r+4))

theorem firingLayerStepTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (i : Fin d) (j : Fin r)
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    firingLayerStepTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (firingWork d (reactantStart d r j.val) (r+i.val*d) (r+i.val*d)
          (firingBase d r i.val+j.val) j.val fuel) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (firingWork d (reactantStart d r (j.val+1)) (r+i.val*d) (r+i.val*d)
          (firingBase d r i.val+(j.val+1)) (j.val+1) fuel)
        (ys++SAT.CNF.encode (firingClauses Q i j)))
      (firingLayerStepBudget d r i.val) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let p := reactantStart d r j.val
  let b := r+i.val*d
  let f := firingBase d r i.val+j.val
  let zs := ys++SAT.CNF.encode (firingClauses Q i j)
  have hp : Parked inp := parkedInput_parked _
  have h1 := firingRowTM_correct Q C i j fuel hf ys
  have h2 := liftTM_frame_correct catalystAdvanceTM 1 (fun _ => regTape j.val)
    (fun _ _ => parked_regTape _) inp inp
    (catalystFamilyWork d (p+d) (b+d) b f fuel)
    (catalystFamilyWork d (p+d+d+d) b b (f+1) fuel) zs zs
    (catalystAdvanceTime d (p+d) (b+d) b f)
    (catalystAdvanceTM_correct d (p+d) (b+d) b f fuel inp zs hf hp)
  change (catalystAdvanceTM.liftTM 1).HoareTime
    (EmitPred inp (firingWork d (p+d) (b+d) b f j.val fuel) zs)
    (EmitPred inp (firingWork d (p+d+d+d) b b (f+1) j.val fuel) zs) _ at h2
  have hw1 := firingWork_parked d (p+d) (b+d) b f j.val fuel hf
  have hw2 := firingWork_parked d (p+d+d+d) b b (f+1) j.val fuel hf
  have h3 := incRegTM_hoareTime (7 : Fin 8) j.val inp
    (firingWork d (p+d+d+d) b b (f+1) j.val fuel) zs hp (fun k _ => hw2 k) rfl
  have ew : Function.update (firingWork d (p+d+d+d) b b (f+1) j.val fuel) 7
      (regTape (j.val+1)) = firingWork d (p+d+d+d) b b (f+1) (j.val+1) fuel := by
    funext k
    fin_cases k <;> simp [firingWork,frameWork,catalystFamilyWork]
  rw [ew] at h3
  have h23 := seqTM_hoareTime _ _ h2 (emitPred_transition hp hw2 zs) h3
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw1 zs) h23
  have ep : p+d+d+d = reactantStart d r (j.val+1) := by dsimp [p,reactantStart]; ring
  rw [ep] at h
  have ef : f+1 = firingBase d r i.val+(j.val+1) := by dsimp [f]; omega
  rw [ef] at h
  apply h.mono_bound
  dsimp [firingLayerStepBudget,catalystAdvanceTime,p,b,f,reactantStart]
  gcongr <;> exact Nat.le_of_lt j.isLt

def firingLayerPrefix {d r : Nat} (Q : CRS (Fin d) (Fin r)) (i : Fin d) (n : Nat) : SAT.CNF :=
  (List.range n).flatMap (fun j => if h : j < r then firingClauses Q i ⟨j,h⟩ else [])

theorem firingLayerPrefix_succ {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (i : Fin d) (j : Fin r) :
    firingLayerPrefix Q i (j.val+1) = firingLayerPrefix Q i j.val ++ firingClauses Q i j := by
  simp [firingLayerPrefix,List.range_succ,j.isLt]

theorem firingLayerPrefix_full {d r : Nat} (Q : CRS (Fin d) (Fin r)) (i : Fin d) :
    firingLayerPrefix Q i r = (List.finRange r).flatMap (firingClauses Q i) := by
  unfold firingLayerPrefix
  change ((List.range r).map _).flatten = ((List.finRange r).map _).flatten
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj hk
    have hjr : j < r := by simpa using hj
    simp [hjr]

def firingLayerTM : TM 8 := forRegTM firingLayerStepTM 5

theorem firingLayerTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (i : Fin d) (ys : List Bool) :
    firingLayerTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (firingWork d (reactantStart d r 0) (r+i.val*d) (r+i.val*d)
          (firingBase d r i.val) 0 (regTape r)) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (firingWork d (reactantStart d r r) (r+i.val*d) (r+i.val*d)
          (firingBase d r i.val+r) r (regTape r))
        (ys++SAT.CNF.encode ((List.finRange r).flatMap (firingClauses Q i))))
      (r*(firingLayerStepBudget d r i.val+2)+r+2) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let W := fun j => firingWork d (reactantStart d r j) (r+i.val*d) (r+i.val*d)
    (firingBase d r i.val+j) j (regTape r)
  let Y := fun j => ys++SAT.CNF.encode (firingLayerPrefix Q i j)
  have hp : Parked inp := parkedInput_parked _
  have hw : ∀ j k, Parked (W j k) := fun j =>
    firingWork_parked _ _ _ _ _ _ _ (parked_regTape r)
  have hb : ∀ j, j < r → firingLayerStepTM.HoareTime
      (EmitPred inp (Function.update (W j) 5 ⟨j+2,regCells r⟩) (Y j))
      (EmitPred inp (Function.update (W (j+1)) 5 ⟨j+2,regCells r⟩) (Y (j+1)))
      (firingLayerStepBudget d r i.val) := by
    intro j hj
    have h := firingLayerStepTM_correct Q C i ⟨j,hj⟩ ⟨j+2,regCells r⟩
      (parked_regCells (by omega)) (Y j)
    have ew (k : Nat) : Function.update (W k) 5 ⟨j+2,regCells r⟩ =
        firingWork d (reactantStart d r k) (r+i.val*d) (r+i.val*d)
          (firingBase d r i.val+k) k ⟨j+2,regCells r⟩ := by
      funext l
      fin_cases l <;> simp [W,firingWork,frameWork,catalystFamilyWork]
    rw [ew,ew]
    have ey : Y j++SAT.CNF.encode (firingClauses Q i ⟨j,hj⟩) = Y (j+1) := by
      simp [Y,firingLayerPrefix_succ Q i ⟨j,hj⟩,SAT.CNF.encode_append,List.append_assoc]
    rw [ey] at h
    exact h
  have h := forRegTM_hoareTime firingLayerStepTM (5 : Fin 8) r inp W Y
    (firingLayerStepBudget d r i.val) hp (fun _ => rfl) (fun j k _ => hw j k) hb
  dsimp only [Y] at h
  rw [firingLayerPrefix_full] at h
  have hp0 : firingLayerPrefix Q i 0 = [] := by rfl
  rw [hp0] at h
  unfold EmitPred at h ⊢
  dsimp only [firingLayerTM, W, inp] at h ⊢
  rw [SAT.CNF.encode_nil, List.append_nil] at h
  exact h

theorem firingLayerTime_le (d r i N : Nat) (hd : d ≤ N) (hr : r ≤ N) (hi : i ≤ N) :
    r*(firingLayerStepBudget d r i+2)+r+2 ≤ 1024*(N+1)^5 := by
  calc
    _ ≤ N*(firingLayerStepBudget N N N+2)+N+2 := by
      unfold firingLayerStepBudget catalystAdvanceTime reactantStart firingBase
      gcongr
    _ ≤ 1024*(N+1)^5 := by
      unfold firingLayerStepBudget catalystAdvanceTime reactantStart firingBase
      ring_nf
      omega

end IrrRAFEnumeration.CompletionQuery

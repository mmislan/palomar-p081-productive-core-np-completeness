module

public import proofs.IrrRAFEnumeration.CompletionSupportClause

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def supportLayerWork (count stride p f a v savedPos savedFire : Nat) (fuel : Tape) : Fin 10 → Tape :=
  frameWork (m := 3) (supportWork count stride p f a v)
    (fun k => if k = 7 then fuel else if k = 8 then regTape savedPos else regTape savedFire)

theorem supportLayerWork_parked (count stride p f a v s t : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ k, Parked (supportLayerWork count stride p f a v s t fuel k) := by
  intro k
  fin_cases k <;> simp only [supportLayerWork,frameWork,supportWork,strideWork] <;>
    first | exact hf | exact parked_regTape _

def supportNextMoleculeTM : TM 10 :=
  seqTM (incRegTM 8) (seqTM (copyIntoTM 8 1)
    (seqTM (copyIntoTM 9 2) (seqTM (incRegTM 5) (incRegTM 6))))

def supportNextMoleculeTime (p f a v s t : Nat) :=
  (2*s+4)+1+(2*p+5+(s+1)*(2*(s+1)+6)+(s+1)+2)+1+
    (2*f+5+t*(2*t+6)+t+2)+1+(2*a+4)+1+(2*v+4)

theorem supportNextMoleculeTM_correct (count stride p f a v s t : Nat) (fuel inp : Tape)
    (ys : List Bool) (hf : Parked fuel) (hp : Parked inp) :
    supportNextMoleculeTM.HoareTime
      (EmitPred inp (supportLayerWork count stride p f a v s t fuel) ys)
      (EmitPred inp (supportLayerWork count stride (s+1) t (a+1) (v+1) (s+1) t fuel) ys)
      (supportNextMoleculeTime p f a v s t) := by
  let W := fun p f a v s => supportLayerWork count stride p f a v s t fuel
  have hw : ∀ p f a v s k, Parked (W p f a v s k) :=
    fun p f a v s => supportLayerWork_parked count stride p f a v s t fuel hf
  have h1 := incRegTM_hoareTime (8 : Fin 10) s inp (W p f a v s) ys hp
    (fun k _ => hw p f a v s k) rfl
  have e1 : Function.update (W p f a v s) 8 (regTape (s+1)) = W p f a v (s+1) := by
    funext k; fin_cases k <;> simp [W,supportLayerWork,frameWork,supportWork,strideWork]
  rw [e1] at h1
  have h2 := copyIntoTM_hoareTime (8 : Fin 10) 1 (by decide) (s+1) p inp (W p f a v (s+1)) ys hp
    (fun k _ => hw p f a v (s+1) k) rfl rfl
  have e2 : Function.update (W p f a v (s+1)) 1 (regTape (s+1)) = W (s+1) f a v (s+1) := by
    funext k; fin_cases k <;> simp [W,supportLayerWork,frameWork,supportWork,strideWork]
  rw [e2] at h2
  have h3 := copyIntoTM_hoareTime (9 : Fin 10) 2 (by decide) t f inp (W (s+1) f a v (s+1)) ys hp
    (fun k _ => hw (s+1) f a v (s+1) k) rfl rfl
  have e3 : Function.update (W (s+1) f a v (s+1)) 2 (regTape t) = W (s+1) t a v (s+1) := by
    funext k; fin_cases k <;> simp [W,supportLayerWork,frameWork,supportWork,strideWork]
  rw [e3] at h3
  have h4 := incRegTM_hoareTime (5 : Fin 10) a inp (W (s+1) t a v (s+1)) ys hp
    (fun k _ => hw (s+1) t a v (s+1) k) rfl
  have e4 : Function.update (W (s+1) t a v (s+1)) 5 (regTape (a+1)) = W (s+1) t (a+1) v (s+1) := by
    funext k; fin_cases k <;> simp [W,supportLayerWork,frameWork,supportWork,strideWork]
  rw [e4] at h4
  have h5 := incRegTM_hoareTime (6 : Fin 10) v inp (W (s+1) t (a+1) v (s+1)) ys hp
    (fun k _ => hw (s+1) t (a+1) v (s+1) k) rfl
  have e5 : Function.update (W (s+1) t (a+1) v (s+1)) 6 (regTape (v+1)) = W (s+1) t (a+1) (v+1) (s+1) := by
    funext k; fin_cases k <;> simp [W,supportLayerWork,frameWork,supportWork,strideWork]
  rw [e5] at h5
  have h45 := seqTM_hoareTime _ _ h4 (emitPred_transition hp (hw _ _ _ _ _) ys) h5
  have h345 := seqTM_hoareTime _ _ h3 (emitPred_transition hp (hw _ _ _ _ _) ys) h45
  have h2345 := seqTM_hoareTime _ _ h2 (emitPred_transition hp (hw _ _ _ _ _) ys) h345
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp (hw _ _ _ _ _) ys) h2345
  convert h using 1
  · rfl
  · unfold supportNextMoleculeTime
    ring

def supportLayerStepTM : TM 10 :=
  seqTM (supportClauseTM.liftTM 3) supportNextMoleculeTM

def supportLayerStepBudget (d r i : Nat) :=
  supportClauseBudget d r i d+1+
    supportNextMoleculeTime (outputStart d r d+r*(3*d)) (firingBase d r i+r)
      (r+(i+1)*d+d) (r+i*d+d) (outputStart d r d) (firingBase d r i)

theorem supportLayerStepTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (i x : Fin d)
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    supportLayerStepTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (supportLayerWork r (3*d) (outputStart d r x.val) (firingBase d r i.val)
          (r+(i.val+1)*d+x.val) (r+i.val*d+x.val) (outputStart d r x.val) (firingBase d r i.val) fuel) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (supportLayerWork r (3*d) (outputStart d r (x.val+1)) (firingBase d r i.val)
          (r+(i.val+1)*d+(x.val+1)) (r+i.val*d+(x.val+1))
          (outputStart d r (x.val+1)) (firingBase d r i.val) fuel)
        (ys++SAT.CNF.encode [supportClause Q i x]))
      (supportLayerStepBudget d r i.val) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let p := outputStart d r x.val
  let f := firingBase d r i.val
  let a := r+(i.val+1)*d+x.val
  let v := r+i.val*d+x.val
  let zs := ys++SAT.CNF.encode [supportClause Q i x]
  change supportLayerStepTM.HoareTime
    (EmitPred inp (supportLayerWork r (3*d) p f a v p f fuel) ys)
    (EmitPred inp
      (supportLayerWork r (3*d) (outputStart d r (x.val+1)) f
        (r+(i.val+1)*d+(x.val+1)) (r+i.val*d+(x.val+1))
        (outputStart d r (x.val+1)) f fuel) zs)
    (supportLayerStepBudget d r i.val)
  let extra : Fin 10 → Tape := fun k => if k = 7 then fuel else if k = 8 then regTape p else regTape f
  have he : ∀ k, 7 ≤ k.val → Parked (extra k) := by
    intro k _
    by_cases h7 : k = 7
    · simpa [extra,h7] using hf
    · by_cases h8 : k = 8 <;> simp only [extra,h7,h8,↓reduceIte] <;> exact parked_regTape _
  have h1 := liftTM_frame_correct supportClauseTM 3 extra he inp inp
    (supportWork r (3*d) p f a v) (supportWork r (3*d) (p+r*(3*d)) (f+r) a v)
    ys zs (supportClauseBudget d r i.val x.val)
      (supportClauseTM_correct (decC := decC) Q C i x ys)
  change (supportClauseTM.liftTM 3).HoareTime
    (EmitPred inp (supportLayerWork r (3*d) p f a v p f fuel) ys)
    (EmitPred inp (supportLayerWork r (3*d) (p+r*(3*d)) (f+r) a v p f fuel) zs) _ at h1
  have hp : Parked inp := parkedInput_parked _
  have hw := supportLayerWork_parked r (3*d) (p+r*(3*d)) (f+r) a v p f fuel hf
  have h2 := supportNextMoleculeTM_correct r (3*d) (p+r*(3*d)) (f+r) a v p f fuel inp zs hf hp
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw zs) h2
  have ht : supportClauseBudget d r i.val x.val+1+
      supportNextMoleculeTime (p+r*(3*d)) (f+r) a v p f ≤ supportLayerStepBudget d r i.val := by
    dsimp [supportLayerStepBudget,supportClauseBudget,supportNextMoleculeTime,strideStepBudget,
      p,f,a,v,outputStart]
    gcongr <;> exact Nat.le_of_lt x.isLt
  have h' := h.mono_bound ht
  have ep : p+1 = outputStart d r (x.val+1) := by dsimp [p,outputStart]; omega
  rw [ep] at h'
  unfold EmitPred at h' ⊢
  dsimp only [supportLayerStepTM,f,a,v] at h' ⊢
  simpa only [Nat.add_assoc] using h'

def supportLayerPrefix {d r : Nat} (Q : CRS (Fin d) (Fin r)) (i : Fin d) (n : Nat) : SAT.CNF :=
  (List.range n).flatMap (fun x => if h : x < d then [supportClause Q i ⟨x,h⟩] else [])

theorem supportLayerPrefix_succ {d r : Nat} (Q : CRS (Fin d) (Fin r)) (i x : Fin d) :
    supportLayerPrefix Q i (x.val+1) = supportLayerPrefix Q i x.val ++ [supportClause Q i x] := by
  simp [supportLayerPrefix,List.range_succ,x.isLt]

theorem supportLayerPrefix_full {d r : Nat} (Q : CRS (Fin d) (Fin r)) (i : Fin d) :
    supportLayerPrefix Q i d = (List.finRange d).map (supportClause Q i) := by
  have he : (List.range d).map (fun x => if h : x < d then [supportClause Q i ⟨x,h⟩] else []) =
      (List.finRange d).map (fun x => [supportClause Q i x]) := by
    apply List.ext_getElem
    · simp
    · intro x hx hy
      have hxd : x < d := by simpa using hx
      simp [hxd]
  unfold supportLayerPrefix
  change ((List.range d).map _).flatten = _
  rw [he]
  have hm (xs : List (Fin d)) : (xs.map (fun x => [supportClause Q i x])).flatten =
      xs.map (supportClause Q i) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  exact hm _

def supportLayerTM : TM 10 := forRegTM supportLayerStepTM 7

theorem supportLayerTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (i : Fin d) (ys : List Bool) :
    supportLayerTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (supportLayerWork r (3*d) (outputStart d r 0) (firingBase d r i.val)
          (r+(i.val+1)*d) (r+i.val*d) (outputStart d r 0) (firingBase d r i.val) (regTape d)) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (supportLayerWork r (3*d) (outputStart d r d) (firingBase d r i.val)
          (r+(i.val+1)*d+d) (r+i.val*d+d) (outputStart d r d) (firingBase d r i.val) (regTape d))
        (ys++SAT.CNF.encode ((List.finRange d).map (supportClause Q i))))
      (d*(supportLayerStepBudget d r i.val+2)+d+2) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  change supportLayerTM.HoareTime
    (EmitPred inp
      (supportLayerWork r (3*d) (outputStart d r 0) (firingBase d r i.val)
        (r+(i.val+1)*d) (r+i.val*d) (outputStart d r 0)
        (firingBase d r i.val) (regTape d)) ys)
    (EmitPred inp
      (supportLayerWork r (3*d) (outputStart d r d) (firingBase d r i.val)
        (r+(i.val+1)*d+d) (r+i.val*d+d) (outputStart d r d)
        (firingBase d r i.val) (regTape d))
      (ys++SAT.CNF.encode ((List.finRange d).map (supportClause Q i))))
    (d*(supportLayerStepBudget d r i.val+2)+d+2)
  let W := fun x => supportLayerWork r (3*d) (outputStart d r x) (firingBase d r i.val)
    (r+(i.val+1)*d+x) (r+i.val*d+x) (outputStart d r x) (firingBase d r i.val) (regTape d)
  let Y := fun x => ys++SAT.CNF.encode (supportLayerPrefix Q i x)
  have hp : Parked inp := parkedInput_parked _
  have hw : ∀ x k, Parked (W x k) := fun x =>
    supportLayerWork_parked _ _ _ _ _ _ _ _ _ (parked_regTape d)
  have hb : ∀ x, x < d → supportLayerStepTM.HoareTime
      (EmitPred inp (Function.update (W x) 7 ⟨x+2,regCells d⟩) (Y x))
      (EmitPred inp (Function.update (W (x+1)) 7 ⟨x+2,regCells d⟩) (Y (x+1)))
      (supportLayerStepBudget d r i.val) := by
    intro x hx
    have h := supportLayerStepTM_correct (decC := decC) Q C i ⟨x,hx⟩ ⟨x+2,regCells d⟩
      (parked_regCells (by omega)) (Y x)
    have ew (j : Nat) : Function.update (W j) 7 ⟨x+2,regCells d⟩ =
        supportLayerWork r (3*d) (outputStart d r j) (firingBase d r i.val)
          (r+(i.val+1)*d+j) (r+i.val*d+j) (outputStart d r j) (firingBase d r i.val) ⟨x+2,regCells d⟩ := by
      funext k; fin_cases k <;> simp [W,supportLayerWork,frameWork,supportWork,strideWork]
    rw [ew,ew]
    have ey : Y x++SAT.CNF.encode [supportClause Q i ⟨x,hx⟩] = Y (x+1) := by
      simp [Y,supportLayerPrefix_succ Q i ⟨x,hx⟩,SAT.CNF.encode_append,List.append_assoc]
    rw [ey] at h
    exact h
  have h := forRegTM_hoareTime supportLayerStepTM (7 : Fin 10) d inp W Y
    (supportLayerStepBudget d r i.val) hp (fun _ => rfl) (fun x k _ => hw x k) hb
  dsimp only [Y] at h
  rw [supportLayerPrefix_full] at h
  have hp0 : supportLayerPrefix Q i 0 = [] := by rfl
  rw [hp0] at h
  unfold EmitPred at h ⊢
  dsimp only [supportLayerTM,W] at h ⊢
  rw [SAT.CNF.encode_nil,List.append_nil,add_zero,← Nat.add_assoc] at h
  exact h

theorem supportLayerTime_le (d r i N : Nat) (hd : d ≤ N) (hr : r ≤ N) (hi : i ≤ N) :
    d*(supportLayerStepBudget d r i+2)+d+2 ≤ 16384*(N+1)^5 := by
  calc
    _ ≤ N*(supportLayerStepBudget N N N+2)+N+2 := by
      unfold supportLayerStepBudget supportClauseBudget supportNextMoleculeTime
        strideStepBudget outputStart firingBase
      gcongr
    _ ≤ 16384*(N+1)^5 := by
      unfold supportLayerStepBudget supportClauseBudget supportNextMoleculeTime
        strideStepBudget outputStart firingBase
      ring_nf
      omega

end IrrRAFEnumeration.CompletionQuery

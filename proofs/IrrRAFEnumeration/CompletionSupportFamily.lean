module

public import proofs.IrrRAFEnumeration.CompletionSupportLayer

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def supportOuterWork (r stride p f a v s t d start : Nat) (fuel : Tape) : Fin 12 → Tape :=
  frameWork (m := 2) (supportLayerWork r stride p f a v s t (regTape d))
    (fun k => if k = 10 then regTape start else fuel)

theorem supportOuterWork_parked (r stride p f a v s t d start : Nat) (fuel : Tape)
    (hf : Parked fuel) : ∀ k, Parked (supportOuterWork r stride p f a v s t d start fuel k) := by
  intro k
  fin_cases k <;> simp only [supportOuterWork,frameWork,supportLayerWork,supportWork,strideWork] <;>
    first | exact hf | exact parked_regTape _

def supportNextLayerTM : TM 12 :=
  seqTM (addIntoTM 0 9) (seqTM (copyIntoTM 9 2)
    (seqTM (copyIntoTM 10 8) (copyIntoTM 10 1)))

def supportNextLayerTime (r p f s t start : Nat) :=
  (r*(2*(t+r)+6)+r+2)+1+(2*f+5+(t+r)*(2*(t+r)+6)+(t+r)+2)+1+
    (2*s+5+start*(2*start+6)+start+2)+1+(2*p+5+start*(2*start+6)+start+2)

theorem supportNextLayerTM_correct (r stride p f a v s t d start : Nat) (fuel inp : Tape)
    (ys : List Bool) (hf : Parked fuel) (hp : Parked inp) :
    supportNextLayerTM.HoareTime
      (EmitPred inp (supportOuterWork r stride p f a v s t d start fuel) ys)
      (EmitPred inp (supportOuterWork r stride start (t+r) a v start (t+r) d start fuel) ys)
      (supportNextLayerTime r p f s t start) := by
  let W := fun p f s t => supportOuterWork r stride p f a v s t d start fuel
  have hw : ∀ p f s t k, Parked (W p f s t k) :=
    fun p f s t => supportOuterWork_parked r stride p f a v s t d start fuel hf
  have h1 := addIntoTM_hoareTime (0 : Fin 12) 9 (by decide) r t inp (W p f s t) ys hp
    (fun k _ => hw p f s t k) rfl rfl
  have e1 : Function.update (W p f s t) 9 (regTape (t+r)) = W p f s (t+r) := by
    funext k; fin_cases k <;> simp [W,supportOuterWork,frameWork,supportLayerWork,supportWork,strideWork]
  rw [e1] at h1
  have h2 := copyIntoTM_hoareTime (9 : Fin 12) 2 (by decide) (t+r) f inp (W p f s (t+r)) ys hp
    (fun k _ => hw p f s (t+r) k) rfl rfl
  have e2 : Function.update (W p f s (t+r)) 2 (regTape (t+r)) = W p (t+r) s (t+r) := by
    funext k; fin_cases k <;> simp [W,supportOuterWork,frameWork,supportLayerWork,supportWork,strideWork]
  rw [e2] at h2
  have h3 := copyIntoTM_hoareTime (10 : Fin 12) 8 (by decide) start s inp (W p (t+r) s (t+r)) ys hp
    (fun k _ => hw p (t+r) s (t+r) k) rfl rfl
  have e3 : Function.update (W p (t+r) s (t+r)) 8 (regTape start) = W p (t+r) start (t+r) := by
    funext k; fin_cases k <;> simp [W,supportOuterWork,frameWork,supportLayerWork,supportWork,strideWork]
  rw [e3] at h3
  have h4 := copyIntoTM_hoareTime (10 : Fin 12) 1 (by decide) start p inp (W p (t+r) start (t+r)) ys hp
    (fun k _ => hw p (t+r) start (t+r) k) rfl rfl
  have e4 : Function.update (W p (t+r) start (t+r)) 1 (regTape start) = W start (t+r) start (t+r) := by
    funext k; fin_cases k <;> simp [W,supportOuterWork,frameWork,supportLayerWork,supportWork,strideWork]
  rw [e4] at h4
  have h34 := seqTM_hoareTime _ _ h3 (emitPred_transition hp (hw _ _ _ _) ys) h4
  have h234 := seqTM_hoareTime _ _ h2 (emitPred_transition hp (hw _ _ _ _) ys) h34
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp (hw _ _ _ _) ys) h234
  convert h using 1
  · rfl
  · unfold supportNextLayerTime
    ring

def supportFamilyStepTM : TM 12 :=
  seqTM (supportLayerTM.liftTM 2) supportNextLayerTM

def supportFamilyStepBudget (d r : Nat) :=
  d*(supportLayerStepBudget d r d+2)+d+2+1+
    supportNextLayerTime r (outputStart d r d) (firingBase d r d)
      (outputStart d r d) (firingBase d r d) (outputStart d r 0)

def supportLayerClauses {d r : Nat} (Q : CRS (Fin d) (Fin r)) (i : Fin d) : SAT.CNF :=
  (List.finRange d).map (supportClause Q i)

theorem supportFamilyStepTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (i : Fin d)
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    supportFamilyStepTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r i.val)
          (r+(i.val+1)*d) (r+i.val*d) (outputStart d r 0) (firingBase d r i.val)
          d (outputStart d r 0) fuel) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r (i.val+1))
          (r+(i.val+1+1)*d) (r+(i.val+1)*d) (outputStart d r 0) (firingBase d r (i.val+1))
          d (outputStart d r 0) fuel)
        (ys++SAT.CNF.encode (supportLayerClauses Q i)))
      (supportFamilyStepBudget d r) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let s := outputStart d r 0
  let p := outputStart d r d
  let f := firingBase d r i.val
  let a := r+(i.val+1)*d
  let v := r+i.val*d
  let zs := ys++SAT.CNF.encode (supportLayerClauses Q i)
  let extra : Fin 12 → Tape := fun k => if k = 10 then regTape s else fuel
  have he : ∀ k, 10 ≤ k.val → Parked (extra k) := by
    intro k _
    by_cases hk : k = 10 <;> simp only [extra,hk,↓reduceIte]
    · exact parked_regTape _
    · exact hf
  have h1 := liftTM_frame_correct supportLayerTM 2 extra he inp inp
    (supportLayerWork r (3*d) s f a v s f (regTape d))
    (supportLayerWork r (3*d) p f (a+d) (v+d) p f (regTape d)) ys zs
    (d*(supportLayerStepBudget d r i.val+2)+d+2)
      (supportLayerTM_correct (decC := decC) Q C i ys)
  change (supportLayerTM.liftTM 2).HoareTime
    (EmitPred inp (supportOuterWork r (3*d) s f a v s f d s fuel) ys)
    (EmitPred inp (supportOuterWork r (3*d) p f (a+d) (v+d) p f d s fuel) zs) _ at h1
  have hp : Parked inp := parkedInput_parked _
  have hw := supportOuterWork_parked r (3*d) p f (a+d) (v+d) p f d s fuel hf
  have h2 := supportNextLayerTM_correct r (3*d) p f (a+d) (v+d) p f d s fuel inp zs hf hp
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw zs) h2
  have ht : d*(supportLayerStepBudget d r i.val+2)+d+2+1+
      supportNextLayerTime r p f p f s ≤ supportFamilyStepBudget d r := by
    dsimp [supportFamilyStepBudget,supportLayerStepBudget,supportClauseBudget,supportNextMoleculeTime,
      supportNextLayerTime,strideStepBudget,p,f,s,outputStart,firingBase]
    gcongr <;> exact Nat.le_of_lt i.isLt
  have h' := h.mono_bound ht
  have ea : a+d = r+(i.val+1+1)*d := by dsimp [a]; ring
  have ev : v+d = r+(i.val+1)*d := by dsimp [v]; ring
  have ef : f+r = firingBase d r (i.val+1) := by dsimp [f,firingBase]; ring
  rw [ea,ev,ef] at h'
  exact h'

def supportFamilyPrefix {d r : Nat} (Q : CRS (Fin d) (Fin r)) (n : Nat) : SAT.CNF :=
  (List.range n).flatMap (fun i => if h : i < d then supportLayerClauses Q ⟨i,h⟩ else [])

theorem supportFamilyPrefix_succ {d r : Nat} (Q : CRS (Fin d) (Fin r)) (i : Fin d) :
    supportFamilyPrefix Q (i.val+1) = supportFamilyPrefix Q i.val ++ supportLayerClauses Q i := by
  simp [supportFamilyPrefix,List.range_succ,i.isLt]

theorem supportFamilyPrefix_full {d r : Nat} (Q : CRS (Fin d) (Fin r)) :
    supportFamilyPrefix Q d = (List.finRange d).flatMap (supportLayerClauses Q) := by
  unfold supportFamilyPrefix
  change ((List.range d).map _).flatten = ((List.finRange d).map _).flatten
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hid : i < d := by simpa using hi
    simp [hid]

def supportFamilyTM : TM 12 := forRegTM supportFamilyStepTM 11

theorem supportFamilyTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (ys : List Bool) :
    supportFamilyTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r 0)
          (r+d) r (outputStart d r 0) (firingBase d r 0) d (outputStart d r 0) (regTape d)) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r d)
          (r+(d+1)*d) (r+d*d) (outputStart d r 0) (firingBase d r d) d (outputStart d r 0) (regTape d))
        (ys++SAT.CNF.encode ((List.finRange d).flatMap (supportLayerClauses Q))))
      (d*(supportFamilyStepBudget d r+2)+d+2) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  change supportFamilyTM.HoareTime
    (EmitPred inp
      (supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r 0)
        (r+d) r (outputStart d r 0) (firingBase d r 0)
        d (outputStart d r 0) (regTape d)) ys)
    (EmitPred inp
      (supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r d)
        (r+(d+1)*d) (r+d*d) (outputStart d r 0) (firingBase d r d)
        d (outputStart d r 0) (regTape d))
      (ys++SAT.CNF.encode ((List.finRange d).flatMap (supportLayerClauses Q))))
    (d*(supportFamilyStepBudget d r+2)+d+2)
  let W := fun i => supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r i)
    (r+(i+1)*d) (r+i*d) (outputStart d r 0) (firingBase d r i) d (outputStart d r 0) (regTape d)
  let Y := fun i => ys++SAT.CNF.encode (supportFamilyPrefix Q i)
  have hp : Parked inp := parkedInput_parked _
  have hw : ∀ i k, Parked (W i k) := fun i =>
    supportOuterWork_parked _ _ _ _ _ _ _ _ _ _ _ (parked_regTape d)
  have hb : ∀ i, i < d → supportFamilyStepTM.HoareTime
      (EmitPred inp (Function.update (W i) 11 ⟨i+2,regCells d⟩) (Y i))
      (EmitPred inp (Function.update (W (i+1)) 11 ⟨i+2,regCells d⟩) (Y (i+1)))
      (supportFamilyStepBudget d r) := by
    intro i hi
    have h := supportFamilyStepTM_correct (decC := decC) Q C ⟨i,hi⟩ ⟨i+2,regCells d⟩
      (parked_regCells (by omega)) (Y i)
    have ew (j : Nat) : Function.update (W j) 11 ⟨i+2,regCells d⟩ =
        supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r j)
          (r+(j+1)*d) (r+j*d) (outputStart d r 0) (firingBase d r j)
          d (outputStart d r 0) ⟨i+2,regCells d⟩ := by
      funext k; fin_cases k <;> simp [W,supportOuterWork,frameWork,supportLayerWork,supportWork,strideWork]
    rw [ew,ew]
    have ey : Y i++SAT.CNF.encode (supportLayerClauses Q ⟨i,hi⟩) = Y (i+1) := by
      simp [Y,supportFamilyPrefix_succ Q ⟨i,hi⟩,SAT.CNF.encode_append,List.append_assoc]
    rw [ey] at h
    exact h
  have h := forRegTM_hoareTime supportFamilyStepTM (11 : Fin 12) d inp W Y
    (supportFamilyStepBudget d r) hp (fun _ => rfl) (fun i k _ => hw i k) hb
  dsimp only [Y] at h
  rw [supportFamilyPrefix_full] at h
  have hp0 : supportFamilyPrefix Q 0 = [] := by rfl
  rw [hp0] at h
  unfold EmitPred at h ⊢
  dsimp only [supportFamilyTM,W] at h ⊢
  rw [SAT.CNF.encode_nil,List.append_nil,zero_mul,add_zero,← Nat.add_assoc] at h
  rw [zero_add,one_mul] at h
  exact h

theorem supportFamilyTime_le (d r N : Nat) (hd : d ≤ N) (hr : r ≤ N) :
    d*(supportFamilyStepBudget d r+2)+d+2 ≤ 65536*(N+1)^6 := by
  calc
    _ ≤ N*(supportFamilyStepBudget N N+2)+N+2 := by
      unfold supportFamilyStepBudget supportLayerStepBudget supportClauseBudget supportNextMoleculeTime
        supportNextLayerTime strideStepBudget outputStart firingBase
      gcongr
    _ ≤ 65536*(N+1)^6 := by
      unfold supportFamilyStepBudget supportLayerStepBudget supportClauseBudget supportNextMoleculeTime
        supportNextLayerTime strideStepBudget outputStart firingBase
      ring_nf
      omega

/-- Input-polynomial execution of the complete next-row family. Preparation of
the displayed registers remains part of the original-input base compiler. -/
theorem supportFamilyTM_inputBound {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (ys : List Bool) :
    supportFamilyTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r 0)
          (r+d) r (outputStart d r 0) (firingBase d r 0) d (outputStart d r 0) (regTape d)) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (supportOuterWork r (3*d) (outputStart d r 0) (firingBase d r d)
          (r+(d+1)*d) (r+d*d) (outputStart d r 0) (firingBase d r d) d (outputStart d r 0) (regTape d))
        (ys++SAT.CNF.encode ((List.finRange d).flatMap (supportLayerClauses Q))))
      (65536*((inputBits Q C (Equiv.refl _) (Equiv.refl _)).length+1)^6) := by
  have hd : d ≤ (inputBits Q C (Equiv.refl _) (Equiv.refl _)).length := by
    unfold inputBits
    repeat rw [List.length_append]
    repeat rw [List.length_replicate]
    omega
  have hr : r ≤ (inputBits Q C (Equiv.refl _) (Equiv.refl _)).length := by
    unfold inputBits
    repeat rw [List.length_append]
    repeat rw [List.length_replicate]
    omega
  exact (supportFamilyTM_correct (decC := decC) Q C ys).mono_bound
    (supportFamilyTime_le d r _ hd hr)

end IrrRAFEnumeration.CompletionQuery

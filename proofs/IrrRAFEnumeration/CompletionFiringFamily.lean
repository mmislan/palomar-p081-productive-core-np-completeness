module

public import proofs.IrrRAFEnumeration.CompletionFiringLayer

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def firingOuterWork (d p a b f j r s : Nat) (fuel : Tape) : Fin 10 → Tape :=
  frameWork (m := 2) (firingWork d p a b f j (regTape r))
    (fun k => if k = 8 then regTape s else fuel)

theorem firingOuterWork_parked (d p a b f j r s : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ k, Parked (firingOuterWork d p a b f j r s fuel k) := by
  intro k
  fin_cases k <;> simp only [firingOuterWork,frameWork,firingWork,catalystFamilyWork] <;>
    first | exact hf | exact parked_regTape _

def firingNextLayerTM : TM 10 :=
  seqTM (copyIntoTM 8 1) (seqTM (addIntoTM 0 6)
    (seqTM (copyIntoTM 6 2) (clearRegTM 7)))

def firingNextLayerTime (d p a b j s : Nat) :=
  (2*p+5+s*(2*s+6)+s+2)+1+(d*(2*(b+d)+6)+d+2)+1+
    (2*a+5+(b+d)*(2*(b+d)+6)+(b+d)+2)+1+(2*j+4)

theorem firingNextLayerTM_correct (d p a b f j r s : Nat) (fuel inp : Tape)
    (ys : List Bool) (hf : Parked fuel) (hp : Parked inp) :
    firingNextLayerTM.HoareTime
      (EmitPred inp (firingOuterWork d p a b f j r s fuel) ys)
      (EmitPred inp (firingOuterWork d s (b+d) (b+d) f 0 r s fuel) ys)
      (firingNextLayerTime d p a b j s) := by
  let W := fun p a b j => firingOuterWork d p a b f j r s fuel
  have hw : ∀ p a b j k, Parked (W p a b j k) :=
    fun p a b j => firingOuterWork_parked d p a b f j r s fuel hf
  have h1 := copyIntoTM_hoareTime (8 : Fin 10) 1 (by decide) s p inp (W p a b j) ys hp
    (fun k _ => hw p a b j k) rfl rfl
  have e1 : Function.update (W p a b j) 1 (regTape s) = W s a b j := by
    funext k; fin_cases k <;> simp [W,firingOuterWork,frameWork,firingWork,catalystFamilyWork]
  rw [e1] at h1
  have h2 := addIntoTM_hoareTime (0 : Fin 10) 6 (by decide) d b inp (W s a b j) ys hp
    (fun k _ => hw s a b j k) rfl rfl
  have e2 : Function.update (W s a b j) 6 (regTape (b+d)) = W s a (b+d) j := by
    funext k; fin_cases k <;> simp [W,firingOuterWork,frameWork,firingWork,catalystFamilyWork]
  rw [e2] at h2
  have h3 := copyIntoTM_hoareTime (6 : Fin 10) 2 (by decide) (b+d) a inp (W s a (b+d) j) ys hp
    (fun k _ => hw s a (b+d) j k) rfl rfl
  have e3 : Function.update (W s a (b+d) j) 2 (regTape (b+d)) = W s (b+d) (b+d) j := by
    funext k; fin_cases k <;> simp [W,firingOuterWork,frameWork,firingWork,catalystFamilyWork]
  rw [e3] at h3
  have h4 := clearRegTM_hoareTime (7 : Fin 10) j inp (W s (b+d) (b+d) j) ys hp
    (fun k _ => hw s (b+d) (b+d) j k) rfl
  have e4 : Function.update (W s (b+d) (b+d) j) 7 (regTape 0) = W s (b+d) (b+d) 0 := by
    funext k; fin_cases k <;> simp [W,firingOuterWork,frameWork,firingWork,catalystFamilyWork]
  rw [e4] at h4
  have h34 := seqTM_hoareTime _ _ h3 (emitPred_transition hp (hw _ _ _ _) ys) h4
  have h234 := seqTM_hoareTime _ _ h2 (emitPred_transition hp (hw _ _ _ _) ys) h34
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp (hw _ _ _ _) ys) h234
  convert h using 1
  · rfl
  · unfold firingNextLayerTime
    ring

def firingFamilyStepTM : TM 10 :=
  seqTM (firingLayerTM.liftTM 2) firingNextLayerTM

def firingFamilyStepBudget (d r : Nat) :=
  r*(firingLayerStepBudget d r d+2)+r+2+1+
    firingNextLayerTime d (reactantStart d r r) (r+d*d) (r+d*d) r (reactantStart d r 0)

def firingLayerClauses {d r : Nat} (Q : CRS (Fin d) (Fin r)) (i : Fin d) : SAT.CNF :=
  (List.finRange r).flatMap (firingClauses Q i)

theorem firingFamilyStepTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (i : Fin d)
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    firingFamilyStepTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (firingOuterWork d (reactantStart d r 0) (r+i.val*d) (r+i.val*d)
          (firingBase d r i.val) 0 r (reactantStart d r 0) fuel) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (firingOuterWork d (reactantStart d r 0) (r+(i.val+1)*d) (r+(i.val+1)*d)
          (firingBase d r (i.val+1)) 0 r (reactantStart d r 0) fuel)
        (ys++SAT.CNF.encode (firingLayerClauses Q i)))
      (firingFamilyStepBudget d r) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let s := reactantStart d r 0
  let p := reactantStart d r r
  let b := r+i.val*d
  let f := firingBase d r i.val
  let zs := ys++SAT.CNF.encode (firingLayerClauses Q i)
  let extra : Fin 10 → Tape := fun k => if k = 8 then regTape s else fuel
  have he : ∀ k, 8 ≤ k.val → Parked (extra k) := by
    intro k _
    by_cases hk : k = 8 <;> simp only [extra,hk,↓reduceIte]
    · exact parked_regTape _
    · exact hf
  have h1 := liftTM_frame_correct firingLayerTM 2 extra he inp inp
    (firingWork d s b b f 0 (regTape r)) (firingWork d p b b (f+r) r (regTape r)) ys zs
    (r*(firingLayerStepBudget d r i.val+2)+r+2) (firingLayerTM_correct Q C i ys)
  change (firingLayerTM.liftTM 2).HoareTime
    (EmitPred inp (firingOuterWork d s b b f 0 r s fuel) ys)
    (EmitPred inp (firingOuterWork d p b b (f+r) r r s fuel) zs) _ at h1
  have hp : Parked inp := parkedInput_parked _
  have hw := firingOuterWork_parked d p b b (f+r) r r s fuel hf
  have h2 := firingNextLayerTM_correct d p b b (f+r) r r s fuel inp zs hf hp
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw zs) h2
  have ht : r*(firingLayerStepBudget d r i.val+2)+r+2+1+firingNextLayerTime d p b b r s ≤
      firingFamilyStepBudget d r := by
    dsimp [firingFamilyStepBudget,firingLayerStepBudget,catalystAdvanceTime,
      firingNextLayerTime,p,b,s,reactantStart,firingBase]
    gcongr <;> exact Nat.le_of_lt i.isLt
  have h' := h.mono_bound ht
  have eb : b+d = r+(i.val+1)*d := by dsimp [b]; ring
  have ef : f+r = firingBase d r (i.val+1) := by dsimp [f,firingBase]; ring
  rw [eb,ef] at h'
  exact h'

def firingFamilyPrefix {d r : Nat} (Q : CRS (Fin d) (Fin r)) (n : Nat) : SAT.CNF :=
  (List.range n).flatMap (fun i => if h : i < d then firingLayerClauses Q ⟨i,h⟩ else [])

theorem firingFamilyPrefix_succ {d r : Nat} (Q : CRS (Fin d) (Fin r)) (i : Fin d) :
    firingFamilyPrefix Q (i.val+1) = firingFamilyPrefix Q i.val ++ firingLayerClauses Q i := by
  simp [firingFamilyPrefix,List.range_succ,i.isLt]

theorem firingFamilyPrefix_full {d r : Nat} (Q : CRS (Fin d) (Fin r)) :
    firingFamilyPrefix Q d = (List.finRange d).flatMap (firingLayerClauses Q) := by
  unfold firingFamilyPrefix
  change ((List.range d).map _).flatten = ((List.finRange d).map _).flatten
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hid : i < d := by simpa using hi
    simp [hid]

def firingFamilyTM : TM 10 := forRegTM firingFamilyStepTM 9

theorem firingFamilyTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [decC : DecidableRel C] (ys : List Bool) :
    firingFamilyTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (firingOuterWork d (reactantStart d r 0) r r (firingBase d r 0) 0 r
          (reactantStart d r 0) (regTape d)) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (firingOuterWork d (reactantStart d r 0) (r+d*d) (r+d*d) (firingBase d r d) 0 r
          (reactantStart d r 0) (regTape d))
        (ys++SAT.CNF.encode ((List.finRange d).flatMap (firingLayerClauses Q))))
      (d*(firingFamilyStepBudget d r+2)+d+2) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let W := fun i => firingOuterWork d (reactantStart d r 0) (r+i*d) (r+i*d)
    (firingBase d r i) 0 r (reactantStart d r 0) (regTape d)
  let Y := fun i => ys++SAT.CNF.encode (firingFamilyPrefix Q i)
  have hp : Parked inp := parkedInput_parked _
  have hw : ∀ i k, Parked (W i k) := fun i =>
    firingOuterWork_parked _ _ _ _ _ _ _ _ _ (parked_regTape d)
  have hb : ∀ i, i < d → firingFamilyStepTM.HoareTime
      (EmitPred inp (Function.update (W i) 9 ⟨i+2,regCells d⟩) (Y i))
      (EmitPred inp (Function.update (W (i+1)) 9 ⟨i+2,regCells d⟩) (Y (i+1)))
      (firingFamilyStepBudget d r) := by
    intro i hi
    have h := firingFamilyStepTM_correct (decC := decC) Q C ⟨i,hi⟩ ⟨i+2,regCells d⟩
      (parked_regCells (by omega)) (Y i)
    have ew (j : Nat) : Function.update (W j) 9 ⟨i+2,regCells d⟩ =
        firingOuterWork d (reactantStart d r 0) (r+j*d) (r+j*d) (firingBase d r j)
          0 r (reactantStart d r 0) ⟨i+2,regCells d⟩ := by
      funext k
      fin_cases k <;> simp [W,firingOuterWork,frameWork,firingWork,catalystFamilyWork]
    rw [ew,ew]
    have ey : Y i++SAT.CNF.encode (firingLayerClauses Q ⟨i,hi⟩) = Y (i+1) := by
      simp [Y,firingFamilyPrefix_succ Q ⟨i,hi⟩,SAT.CNF.encode_append,List.append_assoc]
    rw [ey] at h
    exact h
  have h := forRegTM_hoareTime firingFamilyStepTM (9 : Fin 10) d inp W Y
    (firingFamilyStepBudget d r) hp (fun _ => rfl) (fun i k _ => hw i k) hb
  dsimp only [Y] at h
  rw [firingFamilyPrefix_full] at h
  have hp0 : firingFamilyPrefix Q 0 = [] := by rfl
  rw [hp0] at h
  unfold EmitPred at h ⊢
  dsimp only [firingFamilyTM, W, inp] at h ⊢
  rw [SAT.CNF.encode_nil, List.append_nil] at h
  rw [zero_mul, add_zero, ← Nat.add_assoc] at h
  exact h

theorem firingFamilyTime_le (d r N : Nat) (hd : d ≤ N) (hr : r ≤ N) :
    d*(firingFamilyStepBudget d r+2)+d+2 ≤ 4096*(N+1)^6 := by
  calc
    _ ≤ N*(firingFamilyStepBudget N N+2)+N+2 := by
      unfold firingFamilyStepBudget firingLayerStepBudget catalystAdvanceTime
        firingNextLayerTime reactantStart firingBase
      gcongr
    _ ≤ 4096*(N+1)^6 := by
      unfold firingFamilyStepBudget firingLayerStepBudget catalystAdvanceTime
        firingNextLayerTime reactantStart firingBase
      ring_nf
      omega

/-- Uniform input-length bound for the full firing family. The original-input
compiler must still initialize the displayed registers. -/
theorem firingFamilyTM_inputBound {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (ys : List Bool) :
    firingFamilyTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (firingOuterWork d (reactantStart d r 0) r r (firingBase d r 0) 0 r
          (reactantStart d r 0) (regTape d)) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (firingOuterWork d (reactantStart d r 0) (r+d*d) (r+d*d) (firingBase d r d) 0 r
          (reactantStart d r 0) (regTape d))
        (ys++SAT.CNF.encode ((List.finRange d).flatMap (firingLayerClauses Q))))
      (4096*((inputBits Q C (Equiv.refl _) (Equiv.refl _)).length+1)^6) := by
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
  exact (firingFamilyTM_correct Q C ys).mono_bound (firingFamilyTime_le d r _ hd hr)

end IrrRAFEnumeration.CompletionQuery

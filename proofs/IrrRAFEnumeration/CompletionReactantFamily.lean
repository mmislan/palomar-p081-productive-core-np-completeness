module

public import proofs.IrrRAFEnumeration.CompletionCatalystFamily
public import proofs.IrrRAFEnumeration.CompletionReactantRow

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def reactantFamilyStepTM : TM 7 :=
  seqTM (reactantRowTM.liftTM 2) catalystAdvanceTM

def reactantStepBudget (d r : Nat) :=
  d*(5*reactantStart d r r+5*(r+d*d)+3*r+10*d+63)+d+2+1+
    catalystAdvanceTime d (reactantStart d r r+d) (r+d*d+d) (r+d*d) r

theorem reactantFamilyStepTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (j : Fin r)
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    reactantFamilyStepTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystFamilyWork d (reactantStart d r j.val) (r+d*d) (r+d*d) j.val fuel) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystFamilyWork d (reactantStart d r (j.val+1)) (r+d*d) (r+d*d) (j.val+1) fuel)
        (ys++SAT.CNF.encode (reactantClauses Q j)))
      (reactantStepBudget d r) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let p := reactantStart d r j.val
  let b := r+d*d
  let extra : Fin 7 → Tape := fun i => if i = 5 then fuel else regTape b
  have he : ∀ i, 5 ≤ i.val → Parked (extra i) := by
    intro i _
    by_cases hi : i = 5 <;> simp only [extra,hi,↓reduceIte]
    · exact hf
    · exact parked_regTape _
  have h1 := liftTM_frame_correct reactantRowTM 2 extra he inp inp
    (implicationWork j.val (regTape d) p b 0) (implicationWork j.val (regTape d) (p+d) (b+d) 0)
    ys (ys++SAT.CNF.encode (reactantClauses Q j))
    (d*(5*p+5*b+3*j.val+10*d+63)+d+2) (reactantRowTM_correct Q C j ys)
  have ew (p a : Nat) : frameWork (m := 2) (implicationWork j.val (regTape d) p a 0) extra =
      catalystFamilyWork d p a b j.val fuel := by
    funext i
    fin_cases i <;> simp [frameWork,implicationWork,extra,catalystFamilyWork]
  rw [ew,ew] at h1
  have hp : Parked inp := parkedInput_parked _
  have hw := catalystFamilyWork_parked d (p+d) (b+d) b j.val fuel hf
  have h2 := catalystAdvanceTM_correct d (p+d) (b+d) b j.val fuel inp
    (ys++SAT.CNF.encode (reactantClauses Q j)) hf hp
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw _) h2
  have ep : p+d+d+d = reactantStart d r (j.val+1) := by dsimp [p,reactantStart]; ring
  rw [ep] at h
  apply h.mono_bound
  dsimp [reactantStepBudget,catalystAdvanceTime,p,b,reactantStart]
  gcongr <;> exact Nat.le_of_lt j.isLt

def reactantPrefix {d r : Nat} (Q : CRS (Fin d) (Fin r)) (n : Nat) : SAT.CNF :=
  (List.range n).flatMap (fun j => if h : j < r then reactantClauses Q ⟨j,h⟩ else [])

theorem reactantPrefix_succ {d r : Nat} (Q : CRS (Fin d) (Fin r)) (j : Fin r) :
    reactantPrefix Q (j.val+1) = reactantPrefix Q j.val ++ reactantClauses Q j := by
  simp [reactantPrefix,List.range_succ,j.isLt]

theorem reactantPrefix_full {d r : Nat} (Q : CRS (Fin d) (Fin r)) :
    reactantPrefix Q r = (List.finRange r).flatMap (reactantClauses Q) := by
  unfold reactantPrefix
  change ((List.range r).map _).flatten = ((List.finRange r).map _).flatten
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hir : i < r := by simpa using hi
    simp [hir]

def reactantFamilyTM : TM 7 := forRegTM reactantFamilyStepTM 5

theorem reactantFamilyTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (ys : List Bool) :
    reactantFamilyTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystFamilyWork d (reactantStart d r 0) (r+d*d) (r+d*d) 0 (regTape r)) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystFamilyWork d (reactantStart d r r) (r+d*d) (r+d*d) r (regTape r))
        (ys++SAT.CNF.encode ((List.finRange r).flatMap (reactantClauses Q))))
      (r*(reactantStepBudget d r+2)+r+2) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let W := fun j => catalystFamilyWork d (reactantStart d r j) (r+d*d) (r+d*d) j (regTape r)
  let Y := fun j => ys++SAT.CNF.encode (reactantPrefix Q j)
  have hp : Parked inp := parkedInput_parked _
  have hw : ∀ j i, Parked (W j i) := fun j =>
    catalystFamilyWork_parked _ _ _ _ _ _ (parked_regTape r)
  have hb : ∀ j, j < r → reactantFamilyStepTM.HoareTime
      (EmitPred inp (Function.update (W j) 5 ⟨j+2,regCells r⟩) (Y j))
      (EmitPred inp (Function.update (W (j+1)) 5 ⟨j+2,regCells r⟩) (Y (j+1)))
      (reactantStepBudget d r) := by
    intro j hj
    have h := reactantFamilyStepTM_correct Q C ⟨j,hj⟩ ⟨j+2,regCells r⟩
      (parked_regCells (by omega)) (Y j)
    have ew (k : Nat) : Function.update (W k) 5 ⟨j+2,regCells r⟩ =
        catalystFamilyWork d (reactantStart d r k) (r+d*d) (r+d*d) k ⟨j+2,regCells r⟩ := by
      funext i; fin_cases i <;> simp [W,catalystFamilyWork]
    rw [ew,ew]
    have ey : Y j++SAT.CNF.encode (reactantClauses Q ⟨j,hj⟩) = Y (j+1) := by
      simp [Y,reactantPrefix_succ Q ⟨j,hj⟩,SAT.CNF.encode_append,List.append_assoc]
    rw [ey] at h
    exact h
  have h := forRegTM_hoareTime reactantFamilyStepTM (5 : Fin 7) r inp W Y
    (reactantStepBudget d r) hp (fun _ => rfl) (fun j i _ => hw j i) hb
  dsimp only [Y] at h
  rw [reactantPrefix_full] at h
  have hp0 : reactantPrefix Q 0 = [] := by rfl
  rw [hp0] at h
  unfold EmitPred at h ⊢
  dsimp only [reactantFamilyTM, W, inp] at h ⊢
  rw [SAT.CNF.encode_nil, List.append_nil] at h
  exact h

theorem reactantFamilyTime_le (d r N : Nat) (hd : d ≤ N) (hr : r ≤ N) :
    r*(reactantStepBudget d r+2)+r+2 ≤ 512*(N+1)^5 := by
  calc
    _ ≤ N*(reactantStepBudget N N+2)+N+2 := by
      unfold reactantStepBudget catalystAdvanceTime reactantStart
      gcongr
    _ ≤ 512*(N+1)^5 := by
      unfold reactantStepBudget catalystAdvanceTime reactantStart
      ring_nf
      omega

/-- The reactant family's polynomial is charged to the original encoded input.
Register preparation remains an explicit obligation of the full compiler. -/
theorem reactantFamilyTM_inputBound {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (ys : List Bool) :
    reactantFamilyTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystFamilyWork d (reactantStart d r 0) (r+d*d) (r+d*d) 0 (regTape r)) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystFamilyWork d (reactantStart d r r) (r+d*d) (r+d*d) r (regTape r))
        (ys++SAT.CNF.encode ((List.finRange r).flatMap (reactantClauses Q))))
      (512*((inputBits Q C (Equiv.refl _) (Equiv.refl _)).length+1)^5) := by
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
  exact (reactantFamilyTM_correct Q C ys).mono_bound (reactantFamilyTime_le d r _ hd hr)

end IrrRAFEnumeration.CompletionQuery

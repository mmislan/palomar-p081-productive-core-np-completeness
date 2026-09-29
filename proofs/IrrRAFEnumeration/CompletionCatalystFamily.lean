module

public import proofs.IrrRAFEnumeration.CompletionCatalystClause
public import proofs.Complexitylib.Models.TuringMachine.Registers.Arith

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open RAF EnumerationContract SATSource Complexity Complexity.TM

def catalystFamilyWork (d p a b j : Nat) (fuel : Tape) : Fin 7 → Tape :=
  ![regTape d,regTape p,regTape a,regTape 0,regTape j,fuel,regTape b]

theorem catalystFamilyWork_parked (d p a b j : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ i, Parked (catalystFamilyWork d p a b j fuel i) := by
  intro i
  fin_cases i <;> first | exact hf | exact parked_regTape _

def catalystAdvanceTM : TM 7 :=
  seqTM (addIntoTM 0 1) (seqTM (addIntoTM 0 1)
    (seqTM (copyIntoTM 6 2) (incRegTM 4)))

def catalystAdvanceTime (d p a b j : Nat) :=
  (d*(2*(p+d)+6)+d+2)+1+(d*(2*(p+d+d)+6)+d+2)+1+
    ((2*a+4)+1+(b*(2*b+6)+(b+2)))+1+(2*j+4)

theorem catalystAdvanceTM_correct (d p a b j : Nat) (fuel inp : Tape) (ys : List Bool)
    (hf : Parked fuel) (hp : Parked inp) :
    catalystAdvanceTM.HoareTime
      (EmitPred inp (catalystFamilyWork d p a b j fuel) ys)
      (EmitPred inp (catalystFamilyWork d (p+d+d) b b (j+1) fuel) ys)
      (catalystAdvanceTime d p a b j) := by
  let W := fun p a j => catalystFamilyWork d p a b j fuel
  have hw : ∀ p a j i, Parked (W p a j i) :=
    fun p a j => catalystFamilyWork_parked d p a b j fuel hf
  have h1 := addIntoTM_hoareTime (0 : Fin 7) 1 (by decide) d p inp (W p a j) ys hp
    (fun i _ => hw p a j i) rfl rfl
  have e1 : Function.update (W p a j) 1 (regTape (p+d)) = W (p+d) a j := by
    funext i; fin_cases i <;> simp [W,catalystFamilyWork]
  rw [e1] at h1
  have h2 := addIntoTM_hoareTime (0 : Fin 7) 1 (by decide) d (p+d) inp (W (p+d) a j) ys hp
    (fun i _ => hw (p+d) a j i) rfl rfl
  have e2 : Function.update (W (p+d) a j) 1 (regTape (p+d+d)) = W (p+d+d) a j := by
    funext i; fin_cases i <;> simp [W,catalystFamilyWork]
  rw [e2] at h2
  have h3 := copyIntoTM_hoareTime (6 : Fin 7) 2 (by decide) b a inp (W (p+d+d) a j) ys hp
    (fun i _ => hw (p+d+d) a j i) rfl rfl
  have e3 : Function.update (W (p+d+d) a j) 2 (regTape b) = W (p+d+d) b j := by
    funext i; fin_cases i <;> simp [W,catalystFamilyWork]
  rw [e3] at h3
  have h4 := incRegTM_hoareTime (4 : Fin 7) j inp (W (p+d+d) b j) ys hp
    (fun i _ => hw (p+d+d) b j i) rfl
  have e4 : Function.update (W (p+d+d) b j) 4 (regTape (j+1)) = W (p+d+d) b (j+1) := by
    funext i; fin_cases i <;> simp [W,catalystFamilyWork]
  rw [e4] at h4
  have h34 := seqTM_hoareTime _ _ h3 (emitPred_transition hp (hw _ _ _) ys) h4
  have h234 := seqTM_hoareTime _ _ h2 (emitPred_transition hp (hw _ _ _) ys) h34
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp (hw _ _ _) ys) h234
  convert h using 1
  · rfl
  · unfold catalystAdvanceTime
    ring

def catalystFamilyStepTM : TM 7 :=
  seqTM (catalystClauseTM.liftTM 2) catalystAdvanceTM

def catalystStepBudget (d r : Nat) :=
  3*r+d*(5*catalystStart d r r+5*(r+d*d)+10*d+53)+d+16+1+
    catalystAdvanceTime d (catalystStart d r r+d) (r+d*d+d) (r+d*d) r

def catalystClause {d r : Nat} (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (j : Fin r) : SAT.Clause :=
  PositiveCompletionCNF.implies (PositiveCompletionCNF.selectVar j)
    (PositiveCompletionCNF.members (fun x => C x j)
      (PositiveCompletionCNF.rowVar r ⟨d,by omega⟩))

theorem catalystFamilyStepTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (j : Fin r)
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    catalystFamilyStepTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystFamilyWork d (catalystStart d r j.val) (r+d*d) (r+d*d) j.val fuel) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystFamilyWork d (catalystStart d r (j.val+1)) (r+d*d) (r+d*d) (j.val+1) fuel)
        (ys++SAT.CNF.encode [catalystClause C j]))
      (catalystStepBudget d r) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let p := catalystStart d r j.val
  let b := r+d*d
  let extra : Fin 7 → Tape := fun i => if i = 5 then fuel else regTape b
  have he : ∀ i, 5 ≤ i.val → Parked (extra i) := by
    intro i _
    by_cases hi : i = 5 <;> simp only [extra,hi,↓reduceIte]
    · exact hf
    · exact parked_regTape _
  have h1 := liftTM_frame_correct catalystClauseTM 2 extra he inp inp
    (catalystWork d p b j.val) (catalystWork d (p+d) (b+d) j.val)
    ys (ys++SAT.CNF.encode [catalystClause C j])
    (3*j.val+d*(5*p+5*b+10*d+53)+d+16) (catalystClauseTM_correct Q C j ys)
  have ew (p a : Nat) : frameWork (m := 2) (catalystWork d p a j.val) extra =
      catalystFamilyWork d p a b j.val fuel := by
    funext i
    fin_cases i <;> simp [frameWork,catalystWork,maskWork,extra,catalystFamilyWork]
  rw [ew,ew] at h1
  have hp : Parked inp := parkedInput_parked _
  have hw := catalystFamilyWork_parked d (p+d) (b+d) b j.val fuel hf
  have h2 := catalystAdvanceTM_correct d (p+d) (b+d) b j.val fuel inp
    (ys++SAT.CNF.encode [catalystClause C j]) hf hp
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw _) h2
  have ep : p+d+d+d = catalystStart d r (j.val+1) := by dsimp [p,catalystStart]; ring
  rw [ep] at h
  apply h.mono_bound
  dsimp [catalystStepBudget,catalystAdvanceTime,p,b,catalystStart]
  gcongr <;> exact Nat.le_of_lt j.isLt

def catalystPrefix {d r : Nat} (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (n : Nat) : SAT.CNF :=
  (List.range n).flatMap (fun j => if h : j < r then [catalystClause C ⟨j,h⟩] else [])

theorem catalystPrefix_succ {d r : Nat} (C : Catalysis (Fin d) (Fin r))
    [DecidableRel C] (j : Fin r) :
    catalystPrefix C (j.val+1) = catalystPrefix C j.val ++ [catalystClause C j] := by
  unfold catalystPrefix
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
  rw [dite_eq_left j.isLt]

theorem catalystPrefix_full {d r : Nat} (C : Catalysis (Fin d) (Fin r))
    [DecidableRel C] :
    catalystPrefix C r = (List.finRange r).map (catalystClause C) := by
  have he : (List.range r).map (fun j => if h : j < r then [catalystClause C ⟨j,h⟩] else []) =
      (List.finRange r).map (fun j => [catalystClause C j]) := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_map, List.length_range,
        List.length_finRange]
    · intro i hi hj
      have hir : i < r := by
        rw [List.length_map, List.length_range] at hi
        exact hi
      rw [List.getElem_map, List.getElem_range, List.getElem_map,
        List.getElem_finRange]
      rw [dite_eq_left hir]
      rfl
  unfold catalystPrefix
  change ((List.range r).map _).flatten = _
  rw [he]
  have hm (xs : List (Fin r)) :
      (xs.map (fun j => [catalystClause C j])).flatten = xs.map (catalystClause C) := by
    induction xs with
    | nil => rfl
    | cons j xs ih =>
        change [catalystClause C j] ++
          (xs.map (fun j => [catalystClause C j])).flatten =
          catalystClause C j :: xs.map (catalystClause C)
        rw [ih]
        rfl
  exact hm _

def catalystFamilyTM : TM 7 := forRegTM catalystFamilyStepTM 5

theorem catalystFamilyTM_correct {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (ys : List Bool) :
    catalystFamilyTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystFamilyWork d (catalystStart d r 0) (r+d*d) (r+d*d) 0 (regTape r)) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystFamilyWork d (catalystStart d r r) (r+d*d) (r+d*d) r (regTape r))
        (ys++SAT.CNF.encode ((List.finRange r).map (catalystClause C))))
      (r*(catalystStepBudget d r+2)+r+2) := by
  let inp := parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _))
  let W := fun j => catalystFamilyWork d (catalystStart d r j) (r+d*d) (r+d*d) j (regTape r)
  let Y := fun j => ys++SAT.CNF.encode (catalystPrefix C j)
  have hp : Parked inp := parkedInput_parked _
  have hw : ∀ j i, Parked (W j i) := fun j =>
    catalystFamilyWork_parked _ _ _ _ _ _ (parked_regTape r)
  have hb : ∀ j, j < r → catalystFamilyStepTM.HoareTime
      (EmitPred inp (Function.update (W j) 5 ⟨j+2,regCells r⟩) (Y j))
      (EmitPred inp (Function.update (W (j+1)) 5 ⟨j+2,regCells r⟩) (Y (j+1)))
      (catalystStepBudget d r) := by
    intro j hj
    have h := catalystFamilyStepTM_correct Q C ⟨j,hj⟩ ⟨j+2,regCells r⟩
      (parked_regCells (by omega)) (Y j)
    have ew (k : Nat) : Function.update (W k) 5 ⟨j+2,regCells r⟩ =
        catalystFamilyWork d (catalystStart d r k) (r+d*d) (r+d*d) k ⟨j+2,regCells r⟩ := by
      funext i; fin_cases i <;> simp [W,catalystFamilyWork]
    rw [ew,ew]
    have ey : Y j++SAT.CNF.encode [catalystClause C ⟨j,hj⟩] = Y (j+1) := by
      unfold Y
      rw [catalystPrefix_succ C ⟨j,hj⟩, SAT.CNF.encode_append,
        List.append_assoc]
    rw [ey] at h
    exact h
  have h := forRegTM_hoareTime catalystFamilyStepTM (5 : Fin 7) r inp W Y
    (catalystStepBudget d r) hp (fun _ => rfl) (fun j i _ => hw j i) hb
  dsimp only [Y] at h
  rw [catalystPrefix_full] at h
  have hp0 : catalystPrefix C 0 = [] := by rfl
  rw [hp0] at h
  unfold EmitPred at h ⊢
  dsimp only [catalystFamilyTM, W, inp] at h ⊢
  rw [SAT.CNF.encode_nil, List.append_nil] at h
  exact h

theorem catalystFamilyTime_le (d r N : Nat) (hd : d ≤ N) (hr : r ≤ N) :
    r*(catalystStepBudget d r+2)+r+2 ≤ 512*(N+1)^5 := by
  calc
    _ ≤ N*(catalystStepBudget N N+2)+N+2 := by
      unfold catalystStepBudget catalystAdvanceTime catalystStart
      gcongr
    _ ≤ 512*(N+1)^5 := by
      unfold catalystStepBudget catalystAdvanceTime catalystStart
      ring_nf
      omega

/-- The family emitter's polynomial is charged to the original encoded input.
Register preparation remains an explicit obligation of the full compiler. -/
theorem catalystFamilyTM_inputBound {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C] (ys : List Bool) :
    catalystFamilyTM.HoareTime
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystFamilyWork d (catalystStart d r 0) (r+d*d) (r+d*d) 0 (regTape r)) ys)
      (EmitPred (parkedInput (inputBits Q C (Equiv.refl _) (Equiv.refl _)))
        (catalystFamilyWork d (catalystStart d r r) (r+d*d) (r+d*d) r (regTape r))
        (ys++SAT.CNF.encode ((List.finRange r).map (catalystClause C))))
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
  exact (catalystFamilyTM_correct Q C ys).mono_bound (catalystFamilyTime_le d r _ hd hr)

end IrrRAFEnumeration.CompletionQuery

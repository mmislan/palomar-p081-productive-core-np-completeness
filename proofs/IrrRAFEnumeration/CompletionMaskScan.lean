module

public import proofs.IrrRAFEnumeration.CompletionConditionalClause

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

def membershipIndex (s : Γ) : Fin 4 := if s = Γ.one then 1 else 0
def maskWork (fuel : Tape) (pos index flag : Nat) : Fin 4 → Tape :=
  ![fuel,regTape pos,regTape index,regTape flag]

theorem maskWork_parked (fuel : Tape) (pos index flag : Nat) (hf : Parked fuel) :
    ∀ i, Parked (maskWork fuel pos index flag i) := by
  intro i
  fin_cases i <;> first | exact hf | exact parked_regTape _

def maskStepTM : TM 4 :=
  seqTM (symProbeTM membershipIndex 1 3)
    (seqTM (excludedFlagTM 3 2)
      (seqTM (clearRegTM 3) (seqTM (incRegTM 1) (incRegTM 2))))

def missingClause (inp : Tape) (pos index : Nat) : SAT.CNF :=
  if inp.cells pos = Γ.one then [] else [[⟨false,index⟩]]

theorem maskStepTM_correct (inp fuel : Tape) (pos index : Nat) (ys : List Bool)
    (hp : Parked inp) (hh : inp.head = 1) (hs : inp.cells 0 = Γ.start)
    (hf : Parked fuel) :
    maskStepTM.HoareTime (EmitPred inp (maskWork fuel pos index 0) ys)
      (EmitPred inp (maskWork fuel (pos+1) (index+1) 0)
        (ys++SAT.CNF.encode (missingClause inp pos index))) (5*pos+5*index+51) := by
  let bit := decide (inp.cells pos = Γ.one)
  let b : Nat := if bit then 1 else 0
  have hb : b ≤ 1 := by dsimp [b]; split <;> omega
  have hval : (membershipIndex (inp.cells pos)).val = b := by
    by_cases h : inp.cells pos = Γ.one <;> simp [membershipIndex,b,bit,h]
  have hw0 := maskWork_parked fuel pos index 0 hf
  have hwb := maskWork_parked fuel pos index b hf
  have hw1 := maskWork_parked fuel (pos+1) index 0 hf
  have h1 := symProbeTM_hoareTime membershipIndex (1 : Fin 4) 3 (by decide)
    pos 0 inp (maskWork fuel pos index 0) ys hp hh hs hw0 rfl rfl
  rw [hval] at h1
  simp only [Nat.zero_add,Nat.mul_zero,Nat.add_zero] at h1
  have e1 : Function.update (maskWork fuel pos index 0) 3 (regTape b) =
      maskWork fuel pos index b := by funext i; fin_cases i <;> simp [maskWork]
  rw [e1] at h1
  have h2 := excludedFlagTM_correct (3 : Fin 4) 2 index bit inp
    (maskWork fuel pos index b) ys hp hwb rfl rfl
  have ec : (if bit then [] else [[⟨false,index⟩]]) = missingClause inp pos index := by
    simp [bit,missingClause]
  rw [ec] at h2
  let zs := ys++SAT.CNF.encode (missingClause inp pos index)
  have h3 := clearRegTM_hoareTime (3 : Fin 4) b inp (maskWork fuel pos index b) zs
    hp (fun i _ => hwb i) rfl
  have e3 : Function.update (maskWork fuel pos index b) 3 (regTape 0) =
      maskWork fuel pos index 0 := by funext i; fin_cases i <;> simp [maskWork]
  rw [e3] at h3
  have h4 := incRegTM_hoareTime (1 : Fin 4) pos inp (maskWork fuel pos index 0) zs
    hp (fun i _ => hw0 i) rfl
  have e4 : Function.update (maskWork fuel pos index 0) 1 (regTape (pos+1)) =
      maskWork fuel (pos+1) index 0 := by funext i; fin_cases i <;> simp [maskWork]
  rw [e4] at h4
  have h5 := incRegTM_hoareTime (2 : Fin 4) index inp (maskWork fuel (pos+1) index 0) zs
    hp (fun i _ => hw1 i) rfl
  have e5 : Function.update (maskWork fuel (pos+1) index 0) 2 (regTape (index+1)) =
      maskWork fuel (pos+1) (index+1) 0 := by funext i; fin_cases i <;> simp [maskWork]
  rw [e5] at h5
  have h45 := seqTM_hoareTime _ _ h4 (emitPred_transition hp hw1 zs) h5
  have h345 := seqTM_hoareTime _ _ h3 (emitPred_transition hp hw0 zs) h45
  have h2345 := seqTM_hoareTime _ _ h2 (emitPred_transition hp hwb zs) h345
  have hall := seqTM_hoareTime _ _ h1 (emitPred_transition hp hwb ys) h2345
  exact hall.mono_bound (by omega)

def maskClauses (inp : Tape) (pos index : Nat) : Nat → SAT.CNF
  | 0 => []
  | n+1 => maskClauses inp pos index n ++ missingClause inp (pos+n) (index+n)

def maskScanTM : TM 4 := forRegTM maskStepTM 0

theorem maskClauses_eq_flatMap (inp : Tape) (pos index count : Nat) :
    maskClauses inp pos index count = (List.range count).flatMap
      (fun i => missingClause inp (pos+i) (index+i)) := by
  induction count with
  | zero => simp [maskClauses]
  | succ n ih => simp [maskClauses,List.range_succ,ih]

theorem maskClauses_eq_each (inp : Tape) (pos index count : Nat)
    (bits : Fin count → Bool)
    (hbits : ∀ i, inp.cells (pos+i.val) = Γ.ofBool (bits i)) :
    maskClauses inp pos index count = PositiveCompletionCNF.each count
      (fun i => if bits i then [] else [[⟨false,index+i.val⟩]]) := by
  rw [maskClauses_eq_flatMap]
  unfold PositiveCompletionCNF.each
  change ((List.range count).map _).flatten = ((List.finRange count).map _).flatten
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hic : i < count := by simpa using hi
    have hb := hbits ⟨i,hic⟩
    simp only [List.getElem_map,List.getElem_range,List.getElem_finRange]
    unfold missingClause
    rw [hb]
    cases hbit : bits ⟨i,hic⟩ <;> simp [Γ.ofBool,hbit]

theorem maskScanTM_correct (inp : Tape) (pos index count : Nat) (ys : List Bool)
    (hp : Parked inp) (hh : inp.head = 1) (hs : inp.cells 0 = Γ.start) :
    maskScanTM.HoareTime (EmitPred inp (maskWork (regTape count) pos index 0) ys)
      (EmitPred inp (maskWork (regTape count) (pos+count) (index+count) 0)
        (ys++SAT.CNF.encode (maskClauses inp pos index count)))
      (count*(5*pos+5*index+10*count+53)+count+2) := by
  let W := fun i => maskWork (regTape count) (pos+i) (index+i) 0
  let Y := fun i => ys++SAT.CNF.encode (maskClauses inp pos index i)
  have hw : ∀ i j, Parked (W i j) := fun i => maskWork_parked _ _ _ _ (parked_regTape _)
  have hbody : ∀ i, i < count → maskStepTM.HoareTime
      (EmitPred inp (Function.update (W i) 0 ⟨i+2,regCells count⟩) (Y i))
      (EmitPred inp (Function.update (W (i+1)) 0 ⟨i+2,regCells count⟩) (Y (i+1)))
      (5*pos+5*index+10*count+51) := by
    intro i hi
    have hf : Parked (⟨i+2,regCells count⟩ : Tape) := parked_regCells (by omega)
    have h := maskStepTM_correct inp ⟨i+2,regCells count⟩ (pos+i) (index+i) (Y i) hp hh hs hf
    have ew (j : Nat) : Function.update (W j) 0 ⟨i+2,regCells count⟩ =
        maskWork ⟨i+2,regCells count⟩ (pos+j) (index+j) 0 := by
      funext k; fin_cases k <;> simp [W,maskWork]
    rw [ew,ew]
    have ey : Y i++SAT.CNF.encode (missingClause inp (pos+i) (index+i)) = Y (i+1) := by
      simp [Y,maskClauses,SAT.CNF.encode_append,List.append_assoc]
    rw [ey] at h
    simpa [Nat.add_assoc] using h.mono_bound (by omega :
      5*(pos+i)+5*(index+i)+51 ≤ 5*pos+5*index+10*count+51)
  have h := forRegTM_hoareTime maskStepTM (0 : Fin 4) count inp W Y
    (5*pos+5*index+10*count+51) hp (fun _ => rfl) (fun i j _ => hw i j) hbody
  simpa [maskScanTM,W,Y,maskClauses,Nat.add_assoc] using h

end IrrRAFEnumeration.CompletionQuery

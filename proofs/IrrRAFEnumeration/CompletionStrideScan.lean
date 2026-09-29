module

public import proofs.IrrRAFEnumeration.CompletionSelectedScan
public import proofs.Complexitylib.Models.TuringMachine.Registers.Arith

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

def strideWork (stride : Nat) (fuel : Tape) (pos index flag : Nat) : Fin 5 → Tape :=
  ![fuel,regTape pos,regTape index,regTape flag,regTape stride]

theorem strideWork_parked (stride : Nat) (fuel : Tape) (pos index flag : Nat)
    (hf : Parked fuel) : ∀ i, Parked (strideWork stride fuel pos index flag i) := by
  intro i
  fin_cases i <;> first | exact hf | exact parked_regTape _

def strideStepBudget (stride pos index : Nat) :=
  5*pos+5*index+51+(stride*(2*(pos+stride)+6)+stride+2)

def strideStepTM (sign : Bool) : TM 5 :=
  seqTM (symProbeTM membershipIndex 1 3)
    (seqTM (includedLiteralTM sign 3 2)
      (seqTM (clearRegTM 3) (seqTM (addIntoTM 4 1) (incRegTM 2))))

theorem strideStepTM_correct (sign : Bool) (stride : Nat) (inp fuel : Tape) (pos index : Nat) (ys : List Bool)
    (hp : Parked inp) (hh : inp.head = 1) (hs : inp.cells 0 = Γ.start)
    (hf : Parked fuel) :
    (strideStepTM sign).HoareTime (EmitPred inp (strideWork stride fuel pos index 0) ys)
      (EmitPred inp (strideWork stride fuel (pos+stride) (index+1) 0)
        (ys++SAT.Clause.encode (selectedLiteral sign inp pos index))) (strideStepBudget stride pos index) := by
  let bit := decide (inp.cells pos = Γ.one)
  let b : Nat := if bit then 1 else 0
  have hb : b ≤ 1 := by dsimp [b]; split <;> omega
  have hval : (membershipIndex (inp.cells pos)).val = b := by
    by_cases h : inp.cells pos = Γ.one <;> simp [membershipIndex,b,bit,h]
  have hw0 := strideWork_parked stride fuel pos index 0 hf
  have hwb := strideWork_parked stride fuel pos index b hf
  have hw1 := strideWork_parked stride fuel (pos+stride) index 0 hf
  have h1 := symProbeTM_hoareTime membershipIndex (1 : Fin 5) 3 (by decide)
    pos 0 inp (strideWork stride fuel pos index 0) ys hp hh hs hw0 rfl rfl
  rw [hval] at h1
  simp only [Nat.zero_add,Nat.mul_zero,Nat.add_zero] at h1
  have e1 : Function.update (strideWork stride fuel pos index 0) 3 (regTape b) =
      strideWork stride fuel pos index b := by funext i; fin_cases i <;> simp [strideWork]
  rw [e1] at h1
  have h2 := includedLiteralTM_correct sign (3 : Fin 5) 2 index bit inp
    (strideWork stride fuel pos index b) ys hp hwb rfl rfl
  have ec : (if bit then [⟨sign,index⟩] else []) = selectedLiteral sign inp pos index := by
    simp [bit,selectedLiteral]
  rw [ec] at h2
  let zs := ys++SAT.Clause.encode (selectedLiteral sign inp pos index)
  have h3 := clearRegTM_hoareTime (3 : Fin 5) b inp (strideWork stride fuel pos index b) zs
    hp (fun i _ => hwb i) rfl
  have e3 : Function.update (strideWork stride fuel pos index b) 3 (regTape 0) =
      strideWork stride fuel pos index 0 := by funext i; fin_cases i <;> simp [strideWork]
  rw [e3] at h3
  have h4 := addIntoTM_hoareTime (4 : Fin 5) 1 (by decide) stride pos inp (strideWork stride fuel pos index 0) zs
    hp (fun i _ => hw0 i) rfl rfl
  have e4 : Function.update (strideWork stride fuel pos index 0) 1 (regTape (pos+stride)) =
      strideWork stride fuel (pos+stride) index 0 := by funext i; fin_cases i <;> simp [strideWork]
  rw [e4] at h4
  have h5 := incRegTM_hoareTime (2 : Fin 5) index inp (strideWork stride fuel (pos+stride) index 0) zs
    hp (fun i _ => hw1 i) rfl
  have e5 : Function.update (strideWork stride fuel (pos+stride) index 0) 2 (regTape (index+1)) =
      strideWork stride fuel (pos+stride) (index+1) 0 := by funext i; fin_cases i <;> simp [strideWork]
  rw [e5] at h5
  have h45 := seqTM_hoareTime _ _ h4 (emitPred_transition hp hw1 zs) h5
  have h345 := seqTM_hoareTime _ _ h3 (emitPred_transition hp hw0 zs) h45
  have h2345 := seqTM_hoareTime _ _ h2 (emitPred_transition hp hwb zs) h345
  have hall := seqTM_hoareTime _ _ h1 (emitPred_transition hp hwb ys) h2345
  apply hall.mono_bound
  dsimp [strideStepBudget]
  simp only [Nat.add_assoc]
  norm_num only
  omega

def strideLiterals (sign : Bool) (stride : Nat) (inp : Tape) (pos index : Nat) : Nat → SAT.Clause
  | 0 => []
  | n+1 => strideLiterals sign stride inp pos index n ++
      selectedLiteral sign inp (pos+n*stride) (index+n)

def strideScanTM (sign : Bool) : TM 5 := forRegTM (strideStepTM sign) 0

theorem strideLiterals_eq_flatMap (sign : Bool) (stride : Nat) (inp : Tape)
    (pos index count : Nat) :
    strideLiterals sign stride inp pos index count = (List.range count).flatMap
      (fun i => selectedLiteral sign inp (pos+i*stride) (index+i)) := by
  induction count with
  | zero => simp [strideLiterals]
  | succ n ih => simp [strideLiterals,List.range_succ,ih]

theorem strideScanTM_correct (sign : Bool) (stride : Nat) (inp : Tape)
    (pos index count : Nat) (ys : List Bool)
    (hp : Parked inp) (hh : inp.head = 1) (hs : inp.cells 0 = Γ.start) :
    (strideScanTM sign).HoareTime
      (EmitPred inp (strideWork stride (regTape count) pos index 0) ys)
      (EmitPred inp (strideWork stride (regTape count) (pos+count*stride) (index+count) 0)
        (ys++SAT.Clause.encode (strideLiterals sign stride inp pos index count)))
      (count*(strideStepBudget stride (pos+count*stride) (index+count)+2)+count+2) := by
  let W := fun i => strideWork stride (regTape count) (pos+i*stride) (index+i) 0
  let Y := fun i => ys++SAT.Clause.encode (strideLiterals sign stride inp pos index i)
  have hw : ∀ i j, Parked (W i j) := fun i => strideWork_parked _ _ _ _ _ (parked_regTape _)
  have hb : ∀ i, i < count → (strideStepTM sign).HoareTime
      (EmitPred inp (Function.update (W i) 0 ⟨i+2,regCells count⟩) (Y i))
      (EmitPred inp (Function.update (W (i+1)) 0 ⟨i+2,regCells count⟩) (Y (i+1)))
      (strideStepBudget stride (pos+count*stride) (index+count)) := by
    intro i hi
    have h := strideStepTM_correct sign stride inp ⟨i+2,regCells count⟩
      (pos+i*stride) (index+i) (Y i) hp hh hs (parked_regCells (by omega))
    have ew (j : Nat) : Function.update (W j) 0 ⟨i+2,regCells count⟩ =
        strideWork stride ⟨i+2,regCells count⟩ (pos+j*stride) (index+j) 0 := by
      funext k; fin_cases k <;> simp [W,strideWork]
    rw [ew,ew]
    have ey : Y i++SAT.Clause.encode (selectedLiteral sign inp (pos+i*stride) (index+i)) =
        Y (i+1) := by
      simp [Y,strideLiterals,clause_encode_append,List.append_assoc]
    rw [ey] at h
    have ht : strideStepBudget stride (pos+i*stride) (index+i) ≤
        strideStepBudget stride (pos+count*stride) (index+count) := by
      unfold strideStepBudget
      gcongr
    simpa [Nat.add_mul,Nat.add_assoc] using h.mono_bound ht
  have h := forRegTM_hoareTime (strideStepTM sign) (0 : Fin 5) count inp W Y
    (strideStepBudget stride (pos+count*stride) (index+count)) hp
    (fun _ => rfl) (fun i j _ => hw i j) hb
  simpa [strideScanTM,W,Y,strideLiterals,Nat.add_assoc] using h

def strideClauseTM (sign : Bool) : TM 5 :=
  seqTM (strideScanTM sign) (emitBitsTM [true,false])

theorem strideClauseTM_correct (sign : Bool) (stride : Nat) (inp : Tape)
    (pos index count : Nat) (ys : List Bool)
    (hp : Parked inp) (hh : inp.head = 1) (hs : inp.cells 0 = Γ.start) :
    (strideClauseTM sign).HoareTime
      (EmitPred inp (strideWork stride (regTape count) pos index 0) ys)
      (EmitPred inp (strideWork stride (regTape count) (pos+count*stride) (index+count) 0)
        (ys++SAT.CNF.encode [strideLiterals sign stride inp pos index count]))
      (count*(strideStepBudget stride (pos+count*stride) (index+count)+2)+count+6) := by
  have h1 := strideScanTM_correct sign stride inp pos index count ys hp hh hs
  have hw := strideWork_parked stride (regTape count) (pos+count*stride) (index+count) 0
    (parked_regTape count)
  have h2 := emitBitsTM_hoareTime [true,false] inp
    (strideWork stride (regTape count) (pos+count*stride) (index+count) 0)
    (ys++SAT.Clause.encode (strideLiterals sign stride inp pos index count)) hp hw
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw _) h2
  have h' := h.mono_bound (by omega :
    count*(strideStepBudget stride (pos+count*stride) (index+count)+2)+count+2+1+2 ≤
      count*(strideStepBudget stride (pos+count*stride) (index+count)+2)+count+6)
  unfold EmitPred at h' ⊢
  simpa [strideClauseTM,SAT.CNF.encode_cons,List.append_assoc] using h'

end IrrRAFEnumeration.CompletionQuery


module

public import proofs.IrrRAFEnumeration.CompletionMaskScan

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

def includedLiteralTM {k : Nat} (sign : Bool) (flag index : Fin k) : TM k :=
  onReadTM (some flag) Γ.one (emitLitTM sign index)

theorem includedLiteralTM_correct {k : Nat} (sign : Bool) (flag index : Fin k)
    (v : Nat) (bit : Bool) (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j)) (hi : work index = regTape v)
    (hflag : work flag = regTape (if bit then 1 else 0)) :
    (includedLiteralTM sign flag index).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys++SAT.Clause.encode (if bit then [⟨sign,v⟩] else [])))
      (3*v+13) := by
  have he := emitLitTM_hoareTime sign index v inp work ys hp (fun j _ => hw j)
    (by rw [hi]; exact reg_regT v)
  have h := onRead_emit_correct (some flag) Γ.one (emitLitTM sign index) inp work ys
    ([sign,sign]++List.replicate (2*v) true++[false,true]) (3*v+9) hp hw he
  have h' := h.mono_bound (by omega : 3*v+9+1 ≤ 3*v+13)
  cases bit <;> simpa [includedLiteralTM,selectRead,hflag,Tape.read,regTape,regCells,
    SAT.Clause.encode_cons',Nat.add_assoc] using h'

def selectedStepTM (sign : Bool) : TM 4 :=
  seqTM (symProbeTM membershipIndex 1 3)
    (seqTM (includedLiteralTM sign 3 2)
      (seqTM (clearRegTM 3) (seqTM (incRegTM 1) (incRegTM 2))))

def selectedLiteral (sign : Bool) (inp : Tape) (pos index : Nat) : SAT.Clause :=
  if inp.cells pos = Γ.one then [⟨sign,index⟩] else []

theorem selectedStepTM_correct (sign : Bool) (inp fuel : Tape) (pos index : Nat) (ys : List Bool)
    (hp : Parked inp) (hh : inp.head = 1) (hs : inp.cells 0 = Γ.start)
    (hf : Parked fuel) :
    (selectedStepTM sign).HoareTime (EmitPred inp (maskWork fuel pos index 0) ys)
      (EmitPred inp (maskWork fuel (pos+1) (index+1) 0)
        (ys++SAT.Clause.encode (selectedLiteral sign inp pos index))) (5*pos+5*index+51) := by
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
  have h2 := includedLiteralTM_correct sign (3 : Fin 4) 2 index bit inp
    (maskWork fuel pos index b) ys hp hwb rfl rfl
  have ec : (if bit then [⟨sign,index⟩] else []) = selectedLiteral sign inp pos index := by
    simp [bit,selectedLiteral]
  rw [ec] at h2
  let zs := ys++SAT.Clause.encode (selectedLiteral sign inp pos index)
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

def selectedLiterals (sign : Bool) (inp : Tape) (pos index : Nat) : Nat → SAT.Clause
  | 0 => []
  | n+1 => selectedLiterals sign inp pos index n ++ selectedLiteral sign inp (pos+n) (index+n)

def selectedScanTM (sign : Bool) : TM 4 := forRegTM (selectedStepTM sign) 0

theorem selectedLiterals_eq_flatMap (sign : Bool) (inp : Tape) (pos index count : Nat) :
    selectedLiterals sign inp pos index count = (List.range count).flatMap
      (fun i => selectedLiteral sign inp (pos+i) (index+i)) := by
  induction count with
  | zero => simp [selectedLiterals]
  | succ n ih => simp [selectedLiterals,List.range_succ,ih]

theorem selectedScanTM_correct (sign : Bool) (inp : Tape) (pos index count : Nat) (ys : List Bool)
    (hp : Parked inp) (hh : inp.head = 1) (hs : inp.cells 0 = Γ.start) :
    (selectedScanTM sign).HoareTime (EmitPred inp (maskWork (regTape count) pos index 0) ys)
      (EmitPred inp (maskWork (regTape count) (pos+count) (index+count) 0)
        (ys++SAT.Clause.encode (selectedLiterals sign inp pos index count)))
      (count*(5*pos+5*index+10*count+53)+count+2) := by
  let W := fun i => maskWork (regTape count) (pos+i) (index+i) 0
  let Y := fun i => ys++SAT.Clause.encode (selectedLiterals sign inp pos index i)
  have hw : ∀ i j, Parked (W i j) := fun i => maskWork_parked _ _ _ _ (parked_regTape _)
  have hbody : ∀ i, i < count → (selectedStepTM sign).HoareTime
      (EmitPred inp (Function.update (W i) 0 ⟨i+2,regCells count⟩) (Y i))
      (EmitPred inp (Function.update (W (i+1)) 0 ⟨i+2,regCells count⟩) (Y (i+1)))
      (5*pos+5*index+10*count+51) := by
    intro i hi
    have hf : Parked (⟨i+2,regCells count⟩ : Tape) := parked_regCells (by omega)
    have h := selectedStepTM_correct sign inp ⟨i+2,regCells count⟩ (pos+i) (index+i) (Y i) hp hh hs hf
    have ew (j : Nat) : Function.update (W j) 0 ⟨i+2,regCells count⟩ =
        maskWork ⟨i+2,regCells count⟩ (pos+j) (index+j) 0 := by
      funext k; fin_cases k <;> simp [W,maskWork]
    rw [ew,ew]
    have ey : Y i++SAT.Clause.encode (selectedLiteral sign inp (pos+i) (index+i)) = Y (i+1) := by
      simp [Y,selectedLiterals,clause_encode_append,List.append_assoc]
    rw [ey] at h
    simpa [Nat.add_assoc] using h.mono_bound (by omega :
      5*(pos+i)+5*(index+i)+51 ≤ 5*pos+5*index+10*count+51)
  have h := forRegTM_hoareTime (selectedStepTM sign) (0 : Fin 4) count inp W Y
    (5*pos+5*index+10*count+51) hp (fun _ => rfl) (fun i j _ => hw i j) hbody
  simpa [selectedScanTM,W,Y,selectedLiterals,Nat.add_assoc] using h

/-- A mask contributes one disjunction, including the empty disjunction. This
is the form needed for output blockers and alternative supporting catalysts. -/
def selectedClauseTM (sign : Bool) : TM 4 :=
  seqTM (selectedScanTM sign) (emitBitsTM [true,false])

theorem selectedClauseTM_correct (sign : Bool) (inp : Tape)
    (pos index count : Nat) (ys : List Bool)
    (hp : Parked inp) (hh : inp.head = 1) (hs : inp.cells 0 = Γ.start) :
    (selectedClauseTM sign).HoareTime
      (EmitPred inp (maskWork (regTape count) pos index 0) ys)
      (EmitPred inp (maskWork (regTape count) (pos+count) (index+count) 0)
        (ys++SAT.CNF.encode [selectedLiterals sign inp pos index count]))
      (count*(5*pos+5*index+10*count+53)+count+6) := by
  have h1 := selectedScanTM_correct sign inp pos index count ys hp hh hs
  have hw := maskWork_parked (regTape count) (pos+count) (index+count) 0
    (parked_regTape count)
  have h2 := emitBitsTM_hoareTime [true,false] inp
    (maskWork (regTape count) (pos+count) (index+count) 0)
    (ys++SAT.Clause.encode (selectedLiterals sign inp pos index count)) hp hw
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw _) h2
  have h' := h.mono_bound (by omega :
    count*(5*pos+5*index+10*count+53)+count+2+2+1 ≤
      count*(5*pos+5*index+10*count+53)+count+6)
  unfold EmitPred at h' ⊢
  simpa [selectedClauseTM,SAT.CNF.encode_cons,List.append_assoc] using h'

end IrrRAFEnumeration.CompletionQuery

module

public import proofs.IrrRAFEnumeration.CompletionMaskScan

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

def pairClauseTM {k : Nat} (antecedent index : Fin k) : TM k :=
  seqTM (emitLitTM false antecedent) (unitClauseTM true index)

theorem pairClauseTM_correct {k : Nat} (antecedent index : Fin k) (a v : Nat)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j))
    (ha : work antecedent = regTape a) (hi : work index = regTape v) :
    (pairClauseTM antecedent index).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys++SAT.CNF.encode [[⟨false,a⟩,⟨true,v⟩]]))
      (3*a+3*v+22) := by
  have h1 := emitLitTM_hoareTime false antecedent a inp work ys hp (fun j _ => hw j)
    (by rw [ha]; exact reg_regT a)
  have h2 := unitClauseTM_correct true index v inp work
    (ys++([false,false]++List.replicate (2*a) true++[false,true])) hp hw hi
  have h := seqTM_hoareTime _ _ h1 (emitPred_transition hp hw _) h2
  have h' := h.mono_bound (by omega : (3*a+9)+1+(3*v+12) ≤ 3*a+3*v+22)
  simpa [pairClauseTM,SAT.CNF.encode_cons,SAT.Clause.encode_cons',List.append_assoc] using h'

def includedPairTM {k : Nat} (flag antecedent index : Fin k) : TM k :=
  onReadTM (some flag) Γ.one (pairClauseTM antecedent index)

theorem includedPairTM_correct {k : Nat} (flag antecedent index : Fin k)
    (a v : Nat) (bit : Bool) (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hp : Parked inp) (hw : ∀ j, Parked (work j))
    (ha : work antecedent = regTape a) (hi : work index = regTape v)
    (hflag : work flag = regTape (if bit then 1 else 0)) :
    (includedPairTM flag antecedent index).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys++SAT.CNF.encode (if bit then [[⟨false,a⟩,⟨true,v⟩]] else [])))
      (3*a+3*v+23) := by
  have h := onRead_emit_correct (some flag) Γ.one (pairClauseTM antecedent index)
    inp work ys (SAT.CNF.encode [[⟨false,a⟩,⟨true,v⟩]]) (3*a+3*v+22) hp hw
    (pairClauseTM_correct antecedent index a v inp work ys hp hw ha hi)
  cases bit <;> simpa [includedPairTM,selectRead,hflag,Tape.read,regTape,regCells,Nat.add_assoc] using h

def implicationWork (antecedent : Nat) (fuel : Tape) (pos index flag : Nat) : Fin 5 → Tape :=
  ![fuel,regTape pos,regTape index,regTape flag,regTape antecedent]

theorem implicationWork_parked (antecedent : Nat) (fuel : Tape) (pos index flag : Nat)
    (hf : Parked fuel) : ∀ i, Parked (implicationWork antecedent fuel pos index flag i) := by
  intro i
  fin_cases i <;> first | exact hf | exact parked_regTape _

def implicationStepTM : TM 5 :=
  seqTM (symProbeTM membershipIndex 1 3)
    (seqTM (includedPairTM 3 4 2)
      (seqTM (clearRegTM 3) (seqTM (incRegTM 1) (incRegTM 2))))

def requiredClauses (antecedent : Nat) (inp : Tape) (pos index : Nat) : SAT.CNF :=
  if inp.cells pos = Γ.one then [[⟨false,antecedent⟩,⟨true,index⟩]] else []

theorem implicationStepTM_correct (antecedent : Nat) (inp fuel : Tape) (pos index : Nat) (ys : List Bool)
    (hp : Parked inp) (hh : inp.head = 1) (hs : inp.cells 0 = Γ.start)
    (hf : Parked fuel) :
    implicationStepTM.HoareTime (EmitPred inp (implicationWork antecedent fuel pos index 0) ys)
      (EmitPred inp (implicationWork antecedent fuel (pos+1) (index+1) 0)
        (ys++SAT.CNF.encode (requiredClauses antecedent inp pos index))) (5*pos+5*index+3*antecedent+61) := by
  let bit := decide (inp.cells pos = Γ.one)
  let b : Nat := if bit then 1 else 0
  have hb : b ≤ 1 := by dsimp [b]; split <;> omega
  have hval : (membershipIndex (inp.cells pos)).val = b := by
    by_cases h : inp.cells pos = Γ.one <;> simp [membershipIndex,b,bit,h]
  have hw0 := implicationWork_parked antecedent fuel pos index 0 hf
  have hwb := implicationWork_parked antecedent fuel pos index b hf
  have hw1 := implicationWork_parked antecedent fuel (pos+1) index 0 hf
  have h1 := symProbeTM_hoareTime membershipIndex (1 : Fin 5) 3 (by decide)
    pos 0 inp (implicationWork antecedent fuel pos index 0) ys hp hh hs hw0 rfl rfl
  rw [hval] at h1
  simp only [Nat.zero_add,Nat.mul_zero,Nat.add_zero] at h1
  have e1 : Function.update (implicationWork antecedent fuel pos index 0) 3 (regTape b) =
      implicationWork antecedent fuel pos index b := by funext i; fin_cases i <;> simp [implicationWork]
  rw [e1] at h1
  have h2 := includedPairTM_correct (3 : Fin 5) 4 2 antecedent index bit inp
    (implicationWork antecedent fuel pos index b) ys hp hwb rfl rfl rfl
  have ec : (if bit then [[⟨false,antecedent⟩,⟨true,index⟩]] else []) = requiredClauses antecedent inp pos index := by
    simp [bit,requiredClauses]
  rw [ec] at h2
  let zs := ys++SAT.CNF.encode (requiredClauses antecedent inp pos index)
  have h3 := clearRegTM_hoareTime (3 : Fin 5) b inp (implicationWork antecedent fuel pos index b) zs
    hp (fun i _ => hwb i) rfl
  have e3 : Function.update (implicationWork antecedent fuel pos index b) 3 (regTape 0) =
      implicationWork antecedent fuel pos index 0 := by funext i; fin_cases i <;> simp [implicationWork]
  rw [e3] at h3
  have h4 := incRegTM_hoareTime (1 : Fin 5) pos inp (implicationWork antecedent fuel pos index 0) zs
    hp (fun i _ => hw0 i) rfl
  have e4 : Function.update (implicationWork antecedent fuel pos index 0) 1 (regTape (pos+1)) =
      implicationWork antecedent fuel (pos+1) index 0 := by funext i; fin_cases i <;> simp [implicationWork]
  rw [e4] at h4
  have h5 := incRegTM_hoareTime (2 : Fin 5) index inp (implicationWork antecedent fuel (pos+1) index 0) zs
    hp (fun i _ => hw1 i) rfl
  have e5 : Function.update (implicationWork antecedent fuel (pos+1) index 0) 2 (regTape (index+1)) =
      implicationWork antecedent fuel (pos+1) (index+1) 0 := by funext i; fin_cases i <;> simp [implicationWork]
  rw [e5] at h5
  have h45 := seqTM_hoareTime _ _ h4 (emitPred_transition hp hw1 zs) h5
  have h345 := seqTM_hoareTime _ _ h3 (emitPred_transition hp hw0 zs) h45
  have h2345 := seqTM_hoareTime _ _ h2 (emitPred_transition hp hwb zs) h345
  have hall := seqTM_hoareTime _ _ h1 (emitPred_transition hp hwb ys) h2345
  exact hall.mono_bound (by omega)

def implicationClauses (antecedent : Nat) (inp : Tape) (pos index : Nat) : Nat → SAT.CNF
  | 0 => []
  | n+1 => implicationClauses antecedent inp pos index n ++ requiredClauses antecedent inp (pos+n) (index+n)

def implicationScanTM : TM 5 := forRegTM implicationStepTM 0

theorem implicationClauses_eq_flatMap (antecedent : Nat) (inp : Tape) (pos index count : Nat) :
    implicationClauses antecedent inp pos index count = (List.range count).flatMap
      (fun i => requiredClauses antecedent inp (pos+i) (index+i)) := by
  induction count with
  | zero => simp [implicationClauses]
  | succ n ih => simp [implicationClauses,List.range_succ,ih]

theorem implicationClauses_eq_each (antecedent : Nat) (inp : Tape) (pos index count : Nat)
    (bits : Fin count → Bool)
    (hbits : ∀ i, inp.cells (pos+i.val) = Γ.ofBool (bits i)) :
    implicationClauses antecedent inp pos index count = PositiveCompletionCNF.each count
      (fun i => if bits i then [[⟨false,antecedent⟩,⟨true,index+i.val⟩]] else []) := by
  rw [implicationClauses_eq_flatMap]
  unfold PositiveCompletionCNF.each
  change ((List.range count).map _).flatten = ((List.finRange count).map _).flatten
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hic : i < count := by simpa using hi
    have hb := hbits ⟨i,hic⟩
    simp only [List.getElem_map,List.getElem_range,List.getElem_finRange]
    unfold requiredClauses
    rw [hb]
    cases hbit : bits ⟨i,hic⟩ <;> simp [Γ.ofBool,hbit]

theorem implicationScanTM_correct (antecedent : Nat) (inp : Tape) (pos index count : Nat) (ys : List Bool)
    (hp : Parked inp) (hh : inp.head = 1) (hs : inp.cells 0 = Γ.start) :
    implicationScanTM.HoareTime (EmitPred inp (implicationWork antecedent (regTape count) pos index 0) ys)
      (EmitPred inp (implicationWork antecedent (regTape count) (pos+count) (index+count) 0)
        (ys++SAT.CNF.encode (implicationClauses antecedent inp pos index count)))
      (count*(5*pos+5*index+3*antecedent+10*count+63)+count+2) := by
  let W := fun i => implicationWork antecedent (regTape count) (pos+i) (index+i) 0
  let Y := fun i => ys++SAT.CNF.encode (implicationClauses antecedent inp pos index i)
  have hw : ∀ i j, Parked (W i j) := fun i => implicationWork_parked antecedent _ _ _ _ (parked_regTape _)
  have hbody : ∀ i, i < count → implicationStepTM.HoareTime
      (EmitPred inp (Function.update (W i) 0 ⟨i+2,regCells count⟩) (Y i))
      (EmitPred inp (Function.update (W (i+1)) 0 ⟨i+2,regCells count⟩) (Y (i+1)))
      (5*pos+5*index+3*antecedent+10*count+61) := by
    intro i hi
    have hf : Parked (⟨i+2,regCells count⟩ : Tape) := parked_regCells (by omega)
    have h := implicationStepTM_correct antecedent inp ⟨i+2,regCells count⟩ (pos+i) (index+i) (Y i) hp hh hs hf
    have ew (j : Nat) : Function.update (W j) 0 ⟨i+2,regCells count⟩ =
        implicationWork antecedent ⟨i+2,regCells count⟩ (pos+j) (index+j) 0 := by
      funext k; fin_cases k <;> simp [W,implicationWork]
    rw [ew,ew]
    have ey : Y i++SAT.CNF.encode (requiredClauses antecedent inp (pos+i) (index+i)) = Y (i+1) := by
      simp [Y,implicationClauses,SAT.CNF.encode_append,List.append_assoc]
    rw [ey] at h
    simpa [Nat.add_assoc] using h.mono_bound (by omega :
      5*(pos+i)+5*(index+i)+3*antecedent+61 ≤ 5*pos+5*index+3*antecedent+10*count+61)
  have h := forRegTM_hoareTime implicationStepTM (0 : Fin 5) count inp W Y
    (5*pos+5*index+3*antecedent+10*count+61) hp (fun _ => rfl) (fun i j _ => hw i j) hbody
  simpa [implicationScanTM,W,Y,implicationClauses,Nat.add_assoc] using h

end IrrRAFEnumeration.CompletionQuery

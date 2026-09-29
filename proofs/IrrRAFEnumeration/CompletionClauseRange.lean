module

public import proofs.IrrRAFEnumeration.QueryGuardPreparation
public import proofs.Complexitylib.Models.TuringMachine.Registers.ForReg
public import proofs.Complexitylib.SAT.Encoding
public import proofs.IrrRAFEnumeration.PositiveCompletionCNF

@[expose] public section

namespace IrrRAFEnumeration.CompletionQuery
open SATSource Complexity Complexity.TM

def rangeLiterals (s : Bool) (a v : Nat) : SAT.Clause :=
  (List.range v).map (fun i => ⟨s,a+i⟩)

theorem clause_encode_append (xs ys : SAT.Clause) :
    (xs++ys).encode = xs.encode++ys.encode := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [SAT.Clause.encode_cons',ih,List.append_assoc]

theorem rangeLiterals_encode_succ (s : Bool) (a v : Nat) :
    (rangeLiterals s a (v+1)).encode = (rangeLiterals s a v).encode ++
      ([s,s]++List.replicate (2*(a+v)) true++[false,true]) := by
  simp [rangeLiterals,List.range_succ,List.map_append,clause_encode_append,
    SAT.Clause.encode_cons']

def rangeLiteralBody {k : Nat} (s : Bool) (index : Fin k) : TM k :=
  seqTM (emitLitTM s index) (incRegTM index)

def rangeClauseTM {k : Nat} (s : Bool) (fuel index : Fin k) : TM k :=
  seqTM (forRegTM (rangeLiteralBody s index) fuel) (emitBitsTM [true,false])

theorem rangeLiterals_selection (r : Nat) :
    rangeLiterals true 0 r = PositiveCompletionCNF.positive
      ((List.finRange r).map PositiveCompletionCNF.selectVar) := by
  apply List.ext_getElem
  · simp [rangeLiterals,PositiveCompletionCNF.positive]
  · intro i hi hj
    simp [rangeLiterals,PositiveCompletionCNF.positive,PositiveCompletionCNF.selectVar]

theorem rangeClauseTM_correct {k : Nat} (s : Bool) (fuel index : Fin k)
    (hne : index ≠ fuel) (a v : Nat) (inp : Tape) (work : Fin k → Tape)
    (ys : List Bool) (hp : Parked inp) (hw : ∀ j, Parked (work j))
    (hf : work fuel = regTape v) (hi : work index = regTape a) :
    (rangeClauseTM s fuel index).HoareTime (EmitPred inp work ys)
      (EmitPred inp (Function.update work index (regTape (a+v)))
        (ys ++ SAT.CNF.encode [rangeLiterals s a v]))
      (v*(5*(a+v)+16)+v+5) := by
  let W := fun i => Function.update work index (regTape (a+i))
  let Y := fun i => ys++(rangeLiterals s a i).encode
  have hwp : ∀ i j, Parked (W i j) := fun i => updateReg_parked work hw index (a+i)
  have hwf : ∀ i, W i fuel = regTape v := by
    intro i
    simpa [W,Function.update_of_ne hne.symm] using hf
  have hbody : ∀ i, i < v → (rangeLiteralBody s index).HoareTime
      (EmitPred inp (Function.update (W i) fuel ⟨i+2,regCells v⟩) (Y i))
      (EmitPred inp (Function.update (W (i+1)) fuel ⟨i+2,regCells v⟩) (Y (i+1)))
      (5*(a+v)+14) := by
    intro i hiv
    let V := Function.update (W i) fuel (⟨i+2,regCells v⟩ : Tape)
    have hv : ∀ j, Parked (V j) := by
      intro j
      by_cases hj : j = fuel
      · subst j
        simpa [V] using (parked_regCells (v := v) (by omega : 1 ≤ i+2))
      · simpa [V,Function.update_of_ne hj] using hwp i j
    have hvi : V index = regTape (a+i) := by simp [V,W,Function.update_of_ne hne]
    have he := emitLitTM_hoareTime s index (a+i) inp V (Y i) hp
      (fun j _ => hv j) (by rw [hvi]; exact reg_regT _)
    have hn := incRegTM_hoareTime index (a+i) inp V
      (Y i++([s,s]++List.replicate (2*(a+i)) true++[false,true])) hp
      (fun j _ => hv j) hvi
    have hc := seqTM_hoareTime _ _ he (emitPred_transition hp hv _) hn
    have hwout : Function.update V index (regTape (a+i+1)) =
        Function.update (W (i+1)) fuel ⟨i+2,regCells v⟩ := by
      funext j
      by_cases hj : j = index
      · subst j; simp [V,W,Function.update_of_ne hne,Nat.add_assoc]
      · by_cases hjf : j = fuel
        · subst j; simp [V,W,Function.update_of_ne hj]
        · simp [V,W,Function.update_of_ne hj,Function.update_of_ne hjf]
    rw [hwout] at hc
    have hy : Y i++([s,s]++List.replicate (2*(a+i)) true++[false,true]) = Y (i+1) := by
      simp [Y,rangeLiterals_encode_succ,List.append_assoc]
    rw [hy] at hc
    exact hc.mono_bound (by omega)
  have hl := forRegTM_hoareTime (rangeLiteralBody s index) fuel v inp W Y
    (5*(a+v)+14) hp hwf (fun i j _ => hwp i j) hbody
  have ht := emitBitsTM_hoareTime [true,false] inp (W v) (Y v) hp (hwp v)
  have hall := seqTM_hoareTime _ _ hl (emitPred_transition hp (hwp v) _) ht
  have hwzero : W 0 = work := by simp [W,hi]
  unfold EmitPred at hall ⊢
  simpa [rangeClauseTM,hwzero,Y,rangeLiterals,SAT.CNF.encode_cons,
    List.append_assoc,W,Nat.add_assoc] using hall

end IrrRAFEnumeration.CompletionQuery

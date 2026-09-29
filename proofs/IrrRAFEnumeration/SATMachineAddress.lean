module

public import proofs.IrrRAFEnumeration.SATMachineLookup
public import proofs.Complexitylib.Models.TuringMachine.Registers.Horner

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def clauseFlat {n m : Nat} (j : Fin m) (x : Choice n) : Nat :=
  j.val*(n*2)+(choiceOffset n x).val

theorem clauseFlat_lt {n m : Nat} (j : Fin m) (x : Choice n) :
    clauseFlat j x < m*(n*2) := by
  simpa [clauseFlat, finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using
    (finProdFinEquiv (j, choiceOffset n x)).isLt

theorem clausePosition_eq_flat {n m : Nat} (j : Fin m) (x : Choice n) :
    clausePosition j x = clauseFlat j x+(n+m+3) := by
  unfold clausePosition
  rw [cnfHeader_length]
  change n+m+2+((choiceOffset n x).val+(n*2)*j.val)+1 = _
  dsimp only [clauseFlat]
  ring

/-- Six registers: radix, literal, row/position, scratch, header offset, result. -/
def lookupRegisters {n m : Nat} (j : Fin m) (x : Choice n) (i : Fin 6) : Tape :=
  regTape (if i = 0 then n*2 else if i = 1 then (choiceOffset n x).val
    else if i = 2 then j.val else if i = 4 then n+m+3 else 0)

def rowRegisters {n m : Nat} (j : Fin m) (x : Choice n) : Fin 6 → Tape :=
  Function.update (Function.update (lookupRegisters j x) 3 (regTape (clauseFlat j x)))
    2 (regTape (clauseFlat j x))

def positionRegisters {n m : Nat} (j : Fin m) (x : Choice n) : Fin 6 → Tape :=
  Function.update (rowRegisters j x) 2 (regTape (clausePosition j x))

theorem updateReg_parked {k : Nat} (work : Fin k → Tape) (h : ∀ i, Parked (work i))
    (r : Fin k) (v : Nat) : ∀ i, Parked (Function.update work r (regTape v) i) := by
  intro i
  by_cases hi : i = r
  · subst i; rw [Function.update_self]; exact parked_regTape _
  · rw [Function.update_of_ne hi]; exact h i

theorem rowRegisters_parked {n m : Nat} (j : Fin m) (x : Choice n) :
    ∀ i, Parked (rowRegisters j x i) :=
  updateReg_parked _ (updateReg_parked _ (fun _ => parked_regTape _) _ _) _ _

theorem positionRegisters_parked {n m : Nat} (j : Fin m) (x : Choice n) :
    ∀ i, Parked (positionRegisters j x i) :=
  updateReg_parked _ (rowRegisters_parked j x) _ _

/-- A single fixed machine, independent of the SAT instance and query indices. -/
def addressedClauseTM : TM 6 :=
  seqTM (hornerLayerRegTM 0 1 2 3)
    (seqTM (addIntoTM 4 2) (clauseProbeTM 2 5))

/-- Concrete polynomial tape-step bound for address arithmetic plus lookup.
The outer compiler must still initialize the six coordinate registers. -/
theorem addressedClauseTM_correct {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (x : Choice n) (ys : List Bool) :
    addressedClauseTM.HoareTime
      (EmitPred (parkedInput (cnfBits Φ)) (lookupRegisters j x) ys)
      (EmitPred (parkedInput (cnfBits Φ))
        (Function.update (positionRegisters j x) 5
          (regTape (if x ∈ Φ j then 1 else 0))) ys)
      (256*((cnfBits Φ).length+3)^3) := by
  let L := (cnfBits Φ).length
  have hlen : L = n+m+2+m*(n*2) := cnfBits_length Φ
  have hflat := clauseFlat_lt j x
  have hpos := clausePosition_le Φ j x
  have hpeq := clausePosition_eq_flat j x
  have hrad : n*2 ≤ L+1 := by
    have hm : 1 ≤ m := by have hj := j.isLt; omega
    have hmul := Nat.mul_le_mul_right (n*2) hm
    nlinarith
  have hj : j.val ≤ L+1 := by have hh := j.isLt; omega
  have hf : clauseFlat j x ≤ L+1 := by omega
  have ho : n+m+3 ≤ L+1 := by omega
  have hp : Parked (parkedInput (cnfBits Φ)) := parkedInput_parked _
  have h₁ := hornerLayerRegTM_hoareTime
    (X := (0 : Fin 6)) (comp := 1) (tmp := 2) (tmp2 := 3)
    (by decide) (by decide) (by decide) (by decide)
    (L+1) (n*2) j.val (choiceOffset n x).val 0 hrad hj (by omega) hf
    (parkedInput (cnfBits Φ)) (lookupRegisters j x) ys hp
    (fun _ => parked_regTape _)
    (by simp [lookupRegisters]) (by simp [lookupRegisters])
    (by simp [lookupRegisters]) (by simp [lookupRegisters])
  change (hornerLayerRegTM (0 : Fin 6) 1 2 3).HoareTime
    (EmitPred _ (lookupRegisters j x) ys) (EmitPred _ (rowRegisters j x) ys)
    (layerBudget (L+1)) at h₁
  have h₂ := addIntoTM_hoareTime (4 : Fin 6) 2 (by decide)
    (n+m+3) (clauseFlat j x) (parkedInput (cnfBits Φ)) (rowRegisters j x) ys hp
    (fun i _ => rowRegisters_parked j x i)
    (by simp [rowRegisters, lookupRegisters]) (by simp [rowRegisters])
  rw [← hpeq] at h₂
  have h₃ := clauseProbeTM_correct Φ j x (2 : Fin 6) 5 (by decide)
    (positionRegisters j x) ys (positionRegisters_parked j x)
    (by simp [positionRegisters])
    (by simp [positionRegisters, rowRegisters, lookupRegisters])
  have h₂₃ := seqTM_hoareTime _ _ h₂
    (emitPred_transition hp (positionRegisters_parked j x) ys) h₃
  have hall := seqTM_hoareTime _ _ h₁
    (emitPred_transition hp (rowRegisters_parked j x) ys) h₂₃
  have hmul : (n+m+3)*((2*clausePosition j x+4)+2) ≤ (L+1)*(2*L+6) :=
    Nat.mul_le_mul ho (by dsimp only [L]; omega)
  have hb : layerBudget (L+1)+1+
      ((n+m+3)*((2*clausePosition j x+4)+2)+(n+m+3+2)+1+(3*L+20)) ≤
        256*(L+3)^3 := by
    dsimp only [layerBudget, opBudget]
    nlinarith [Nat.zero_le (L^3), Nat.zero_le (L^2)]
  exact hall.mono_bound hb

end IrrRAFEnumeration.SATSource

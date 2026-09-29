module

public import proofs.IrrRAFEnumeration.SATUniformCompiler
public import proofs.Complexitylib.Models.TuringMachine.Registers.Probe

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open SATCompletion CircuitSource Complexity Complexity.TM

def cnfHeader (n m : Nat) : List Bool :=
  List.replicate n true ++ [false] ++ List.replicate m true ++ [false]

theorem cnfBits_eq_header {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    cnfBits Φ = cnfHeader n m ++ cnfBody Φ := by
  simp [cnfBits, cnfHeader, List.append_assoc]

theorem cnfHeader_length (n m : Nat) : (cnfHeader n m).length = n+m+2 := by
  simp [cnfHeader]
  omega

/-- Head position one is the register-machine entry convention. -/
def parkedInput (bits : List Bool) : Tape :=
  { Tape.init (bits.map Γ.ofBool) with head := 1 }

theorem parkedInput_parked (bits : List Bool) : Parked (parkedInput bits) :=
  ⟨by change 1 ≤ 1; omega, Tape.init_ofBool_cells_ne_start bits⟩

def clausePosition {n m : Nat} (j : Fin m) (x : Choice n) : Nat :=
  (cnfHeader n m).length + (finProdFinEquiv (j, choiceOffset n x)).val + 1

theorem clausePosition_le {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (x : Choice n) : clausePosition j x ≤ (cnfBits Φ).length := by
  have hi := (finProdFinEquiv (j, choiceOffset n x)).isLt
  rw [cnfBits_length]
  dsimp only [clausePosition]
  rw [cnfHeader_length]
  omega

theorem clausePosition_cell {n m : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (x : Choice n) :
    (parkedInput (cnfBits Φ)).cells (clausePosition j x) =
      Γ.ofBool (decide (x ∈ Φ j)) := by
  change (Tape.init ((cnfBits Φ).map Γ.ofBool)).cells
    ((cnfHeader n m).length + (finProdFinEquiv (j, choiceOffset n x)).val + 1) = _
  rw [Tape.init_cells_succ, cnfBits_eq_header, List.map_append]
  rw [List.getElem?_append_right (by simp)]
  simp only [List.length_map, Nat.add_sub_cancel_left, List.getElem?_map]
  simp only [cnfBody, List.getElem?_ofFn]
  rw [dite_eq_left (finProdFinEquiv (j, choiceOffset n x)).isLt]
  change Γ.ofBool (decide ((choiceOffset n).symm
    (finProdFinEquiv.symm (finProdFinEquiv (j, choiceOffset n x))).2 ∈
      Φ (finProdFinEquiv.symm (finProdFinEquiv (j, choiceOffset n x))).1)) = _
  simp only [Equiv.symm_apply_apply]

def boolSymbol : Γ → Fin 4
  | .one => 1
  | _ => 0

theorem boolSymbol_ofBool (b : Bool) :
    (boolSymbol (Γ.ofBool b)).val = if b then 1 else 0 := by
  cases b <;> rfl

/-- A fixed finite-state machine probes the indexed CNF cell. The position
register must already be initialized; this theorem does not hide that cost. -/
def clauseProbeTM {k : Nat} (position result : Fin k) : TM k :=
  symProbeTM boolSymbol position result

/-- Concrete tape-step correctness and linear time for a clause lookup.
All tapes except the result register are restored exactly. -/
theorem clauseProbeTM_correct {n m k : Nat} (Φ : Fin m → Finset (Choice n))
    (j : Fin m) (x : Choice n) (position result : Fin k) (hne : position ≠ result)
    (work : Fin k → Tape) (ys : List Bool)
    (hwork : ∀ i, Parked (work i))
    (hpos : work position = regTape (clausePosition j x))
    (hresult : work result = regTape 0) :
    (clauseProbeTM position result).HoareTime
      (EmitPred (parkedInput (cnfBits Φ)) work ys)
      (EmitPred (parkedInput (cnfBits Φ))
        (Function.update work result (regTape (if x ∈ Φ j then 1 else 0))) ys)
      (3*(cnfBits Φ).length+20) := by
  have h := symProbeTM_hoareTime boolSymbol position result hne
    (clausePosition j x) 0 (parkedInput (cnfBits Φ)) work ys
    (parkedInput_parked _) rfl (by simp [parkedInput]) hwork hpos hresult
  have hc := clausePosition_cell Φ j x
  simp only [hc, boolSymbol_ofBool, Nat.zero_add, Nat.mul_zero,
    Nat.add_zero] at h
  have hb : 3*clausePosition j x+20 ≤ 3*(cnfBits Φ).length+20 := by
    have hp := clausePosition_le Φ j x
    omega
  simpa [clauseProbeTM] using h.mono_bound hb

end IrrRAFEnumeration.SATSource

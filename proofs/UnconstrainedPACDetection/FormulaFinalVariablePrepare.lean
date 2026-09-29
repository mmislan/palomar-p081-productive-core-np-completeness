module

public import proofs.UnconstrainedPACDetection.FormulaFinalVariableMerged

@[expose] public section

namespace UnconstrainedPACDetection.FormulaFinalVariablePrepare
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaFinalVariableClauseLoop (bank parked)
open VerifierPairRestore (word word_parked)

def base : TM 20 := placeWorkTM 0 3 (FormulaRailBaseRegisters.machine false)

theorem base_hoare (i c r a b L V C M : Nat) (fuel : Tape) (hf : Parked fuel)
    (inp : Tape) (hi : Parked inp) (ys : List Bool)
    (hL : L ≤ M) (hV : V ≤ M) (hb : b ≤ M) (hbase : FormulaRailBase.value L V V false ≤ M) :
    base.HoareTime (EmitPred inp (bank i c r a b L V C fuel) ys)
      (EmitPred inp (bank i c r a (FormulaRailBase.value L V V false) L V C fuel) ys)
      (40*(opBudget M+1)) := by
  let small : Fin 17 → Tape := fun t => bank i c r a b L V C fuel ⟨t.val,by omega⟩
  have hp : ∀ t, Parked (small t) := fun t => parked _ _ _ _ _ _ _ _ _ hf _
  have h := FormulaRailBaseRegisters.arithmetic_hoare L V V b M false inp small ys hi hp
    rfl rfl rfl rfl hL hV hV hb hbase
  apply FormulaChangingFrame.hoare _ 0 3 inp small
    (FormulaRailBaseRegisters.bank small (FormulaRailBase.value L V V false))
    _ _ ys ys _ (parked _ _ _ _ _ _ _ _ _ hf) _ _ _ h
  · intro t; fin_cases t <;> rfl
  · intro t; fin_cases t <;> simp [FormulaRailBaseRegisters.bank,small,bank,placeWorkIdx]
  · intro t ht
    fin_cases t <;> simp_all [placeWorkInMiddle,bank]

def finish : TM 20 := seqTM (clearRegTM 3) (copyIntoTM 18 17)

theorem finish_hoare (i c r a b L V C f : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    finish.HoareTime (EmitPred inp (bank i c r a b L V C (regTape f)) ys)
      (EmitPred inp (bank i 0 r a b L V C (regTape C)) ys) (2*c+2*f+2*C^2+7*C+12) := by
  have h0 := clearRegTM_hoareTime (3 : Fin 20) c inp (bank i c r a b L V C (regTape f)) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ (parked_regTape _) t) rfl
  have he0 : Function.update (bank i c r a b L V C (regTape f)) 3 (regTape 0) =
      bank i 0 r a b L V C (regTape f) := by
    funext t; fin_cases t <;> simp [bank]
  rw [he0] at h0
  have h1 := copyIntoTM_hoareTime (18 : Fin 20) 17 (by decide) C f inp
    (bank i 0 r a b L V C (regTape f)) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ (parked_regTape _) t) rfl rfl
  have he1 : Function.update (bank i 0 r a b L V C (regTape f)) 17 (regTape C) =
      bank i 0 r a b L V C (regTape C) := by
    funext t; fin_cases t <;> simp [bank]
  rw [he1] at h1
  exact (seqTM_hoareTime _ _ h0
    (emitPred_transition hi (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) h1).mono_bound (by nlinarith)

def machine : TM 20 := seqTM base finish

theorem hoare (φ : SAT.CNF) (i c r a b f : Nat) (ys : List Bool)
    (hb : b ≤ FormulaVariableTailBound.cap φ) :
    machine.HoareTime
      (EmitPred (word φ.encode) (bank i c r a b (levels φ) (varCount φ) φ.length (regTape f)) ys)
      (EmitPred (word φ.encode) (bank i 0 r a (FormulaClauseCursor.base φ)
        (levels φ) (varCount φ) φ.length (regTape φ.length)) ys)
      (40*(opBudget (FormulaVariableTailBound.cap φ)+1)+2*c+2*f+2*φ.length^2+7*φ.length+13) := by
  obtain ⟨hL,hV,_⟩ := FormulaEnumeration.parameter_bounds φ
  have hn := FormulaIndexedGraph.labels_bound φ
  have hbase : FormulaRailBase.value (levels φ) (varCount φ) (varCount φ) false ≤
      FormulaVariableTailBound.cap φ := by
    have he := FormulaClauseCursor.labels φ
    have hh := congrArg List.length he
    simp only [List.length_append,FormulaClauseCursor.initialVertices_length,List.length_map,
      List.length_finRange] at hh
    have hbn : FormulaClauseCursor.base φ ≤ (FormulaIndexedGraph.labels φ).length := by omega
    apply hbn.trans (hn.trans _)
    unfold FormulaVariableTailBound.cap
    nlinarith only [Nat.zero_le φ.encode.length]
  have h0 := base_hoare i c r a b (levels φ) (varCount φ) φ.length
    (FormulaVariableTailBound.cap φ) (regTape f) (parked_regTape _) (word φ.encode) (word_parked _) ys
    (by unfold FormulaVariableTailBound.cap; nlinarith)
    (by unfold FormulaVariableTailBound.cap; nlinarith) hb hbase
  have h1 := finish_hoare i c r a (FormulaClauseCursor.base φ) (levels φ) (varCount φ) φ.length f
    (word φ.encode) (word_parked _) ys
  exact (seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) _) h1).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaFinalVariablePrepare

module

public import proofs.UnconstrainedPACDetection.FormulaRowGate

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRowLoop
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaRowGate (frame)

theorem advance_hoare (φ : SAT.CNF) (k : Nat) (fuel : Tape) (hf : Parked fuel)
    (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    (incRegTM (9 : Fin 28)).HoareTime (EmitPred inp (frame φ k fuel) ys)
      (EmitPred inp (frame φ (k+1) fuel) ys) (2*k+4) := by
  have h := incRegTM_hoareTime (9 : Fin 28) k inp (frame φ k fuel) ys hi
    (fun t _ => FormulaRowQuery.parked _ _ _ _ _ _ _ _ hf t) rfl
  have he : Function.update (frame φ k fuel) 9 (regTape (k+1)) = frame φ (k+1) fuel := by
    funext t; fin_cases t <;> simp [frame,FormulaRowQuery.frame,FormulaAllTails.frame,
      FormulaExternalTailPhase.frame,FormulaAllRailTails.frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,FormulaRailTailReentrant.frame,
      FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he] at h
  exact h

def body (right : Bool) : TM 28 := seqTM (FormulaRowGate.machine right) (incRegTM 9)

def bodyBudget (φ : SAT.CNF) : Nat := FormulaRowGate.budget φ+2*(FormulaIndexedGraph.labels φ).length+5

theorem body_hoare (φ : SAT.CNF) (k : Fin (FormulaIndexedGraph.labels φ).length) (right : Bool)
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    (body right).HoareTime (EmitPred (word φ.encode) (frame φ k.val fuel) ys)
      (EmitPred (word φ.encode) (frame φ (k.val+1) fuel) (ys ++ FormulaRowGate.field φ right k)) (bodyBudget φ) := by
  have h0 := FormulaRowGate.hoare φ k right fuel hf ys
  have h1 := advance_hoare φ k.val fuel hf (word φ.encode) (word_parked _) (ys ++ FormulaRowGate.field φ right k)
  have h := seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) (FormulaRowQuery.parked _ _ _ _ _ _ _ _ hf) _) h1
  have hk := k.isLt
  exact h.mono_bound (by unfold bodyBudget; omega)

def field (φ : SAT.CNF) (right : Bool) (k : Nat) : List Bool :=
  if hk : k<(FormulaIndexedGraph.labels φ).length then FormulaRowGate.field φ right ⟨k,hk⟩ else []

def bits (φ : SAT.CNF) (right : Bool) (k : Nat) : List Bool := (List.range k).flatMap (field φ right)

def machine (right : Bool) : TM 28 := forRegTM (body right) 27

theorem hoare (φ : SAT.CNF) (right : Bool) (ys : List Bool) :
    (machine right).HoareTime
      (EmitPred (word φ.encode) (frame φ 0 (regTape (FormulaIndexedGraph.labels φ).length)) ys)
      (EmitPred (word φ.encode) (frame φ (FormulaIndexedGraph.labels φ).length (regTape (FormulaIndexedGraph.labels φ).length))
        (ys ++ bits φ right (FormulaIndexedGraph.labels φ).length))
      ((FormulaIndexedGraph.labels φ).length*(bodyBudget φ+2)+((FormulaIndexedGraph.labels φ).length+2)) := by
  let N := (FormulaIndexedGraph.labels φ).length
  let w := fun k => frame φ k (regTape N)
  let zs := fun k => ys ++ bits φ right k
  have h := forRegTM_hoareTime (body right) (27 : Fin 28) N (word φ.encode) w zs (bodyBudget φ)
    (word_parked _) (by intro k; rfl)
    (by intro k t _; exact FormulaRowQuery.parked _ _ _ _ _ _ _ _ (parked_regTape _) t) (by
      intro k hk
      let fuel : Tape := ⟨k+2,regCells N⟩
      have hf : Parked fuel := parked_regCells (by omega)
      have he (z : Nat) : Function.update (w z) 27 fuel = frame φ z fuel := by
        funext t; fin_cases t <;> simp [w,frame,FormulaRowQuery.frame]
      have hb := body_hoare φ ⟨k,hk⟩ right fuel hf (zs k)
      have hy : zs (k+1) = zs k ++ field φ right k := by
        simp [zs,bits,List.range_succ,List.flatMap_append,List.append_assoc]
      have hk' : k<(FormulaIndexedGraph.labels φ).length := hk
      rw [he,he,hy]
      have hfin : (⟨k,hk⟩ : Fin (FormulaIndexedGraph.labels φ).length) = ⟨k,hk'⟩ := Fin.ext rfl
      unfold EmitPred at hb
      simpa only [field,dite_eq_left hk',hfin] using hb)
  simpa only [machine,w,zs,bits,List.range_zero,List.flatMap_nil,List.append_nil,N,Nat.add_assoc] using h

end UnconstrainedPACDetection.FormulaRowLoop

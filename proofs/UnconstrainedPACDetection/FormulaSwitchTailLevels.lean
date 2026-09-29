module

public import proofs.UnconstrainedPACDetection.FormulaSwitchTailPorts

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchTailLevels
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (tag index)
open FormulaChangingFrame (extend)

def frame (k r L V C : Nat) (fuel : Tape) : Fin 22 → Tape :=
  extend (FormulaSwitchTailReentrant.frame k r (20*k) L V C) fuel

theorem parked (k r L V C : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ t, Parked (frame k r L V C fuel t) :=
  FormulaChangingFrame.parked _ _ (FormulaSwitchTailReentrant.parked _ _ _ _ _ _) hf

theorem advance_hoare (k r L V C : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    (incRegTM (0 : Fin 21)).HoareTime
      (EmitPred inp (FormulaSwitchTailReentrant.frame k r (20*k+20) L V C) ys)
      (EmitPred inp (FormulaSwitchTailReentrant.frame (k+1) r (20*(k+1)) L V C) ys) (2*k+4) := by
  have h := incRegTM_hoareTime (0 : Fin 21) k inp
    (FormulaSwitchTailReentrant.frame k r (20*k+20) L V C) ys hi
    (fun t _ => FormulaSwitchTailReentrant.parked _ _ _ _ _ _ t) rfl
  have he : Function.update (FormulaSwitchTailReentrant.frame k r (20*k+20) L V C) 0 (regTape (k+1)) =
      FormulaSwitchTailReentrant.frame (k+1) r (20*(k+1)) L V C := by
    funext t; fin_cases t <;> simp [FormulaSwitchTailReentrant.frame,FormulaSwitchTailHeads.frame,
      extend,FormulaSwitchVariableHeads.bank,FormulaSwitchVariableHeads.extend,FormulaRailClauseHeads.extend,
      FormulaAllRailHeads.raw,FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank,Nat.mul_add]
  rw [he] at h
  exact h

def body (right : Bool) (rt : Option Bool) : TM 22 :=
  placeWorkTM 0 1 (seqTM (FormulaSwitchTailPorts.machine right rt 20) (incRegTM 0))

def bodyBudget (φ : SAT.CNF) : Nat := 20*FormulaSwitchTailPorts.stepBudget φ+2*levels φ+6

theorem body_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    (body right (tag r)).HoareTime
      (EmitPred (word φ.encode) (frame i.val (index r) (levels φ) (varCount φ) φ.length fuel) ys)
      (EmitPred (word φ.encode) (frame (i.val+1) (index r) (levels φ) (varCount φ) φ.length fuel)
        (ys ++ FormulaSwitchTailPorts.bits φ i right r 20)) (bodyBudget φ) := by
  have h0 := FormulaSwitchTailPorts.hoare φ i right r 20 (by omega) ys
  have h1 := advance_hoare i.val (index r) (levels φ) (varCount φ) φ.length
    (word φ.encode) (word_parked _) (ys ++ FormulaSwitchTailPorts.bits φ i right r 20)
  have h := seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _)
    (FormulaSwitchTailReentrant.parked _ _ _ _ _ _) _) h1
  have hl := FormulaChangingFrame.append_hoare _ _ _ _ fuel _ _ _
    (FormulaSwitchTailReentrant.parked _ _ _ _ _ _) hf h
  have hi := i.isLt
  exact hl.mono_bound (by unfold bodyBudget; omega)

def field (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  if hk : k<levels φ then FormulaSwitchTailPorts.bits φ ⟨k,hk⟩ right r 20 else []

def bits (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  (List.range k).flatMap (field φ right r)

def machine (right : Bool) (rt : Option Bool) : TM 22 := forRegTM (body right rt) 21

theorem hoare (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine right (tag r)).HoareTime
      (EmitPred (word φ.encode) (frame 0 (index r) (levels φ) (varCount φ) φ.length (regTape (levels φ))) ys)
      (EmitPred (word φ.encode) (frame (levels φ) (index r) (levels φ) (varCount φ) φ.length (regTape (levels φ)))
        (ys ++ bits φ right r (levels φ)))
      (levels φ*(bodyBudget φ+2)+(levels φ+2)) := by
  let L := levels φ
  let w := fun k => frame k (index r) L (varCount φ) φ.length (regTape L)
  let zs := fun k => ys ++ bits φ right r k
  have h := forRegTM_hoareTime (body right (tag r)) (21 : Fin 22) L (word φ.encode) w zs
    (bodyBudget φ) (word_parked _) (by intro k; rfl)
    (by intro k t _; exact parked _ _ _ _ _ _ (parked_regTape _) t) (by
      intro k hk
      let fuel : Tape := ⟨k+2,regCells L⟩
      have hf : Parked fuel := parked_regCells (by omega)
      have he (z : Nat) : Function.update (w z) 21 fuel = frame z (index r) L (varCount φ) φ.length fuel := by
        funext t; fin_cases t <;> simp [w,frame,extend]
      have hb := body_hoare φ ⟨k,hk⟩ right r fuel hf (zs k)
      have hy : zs (k+1) = zs k ++ field φ right r k := by
        simp [zs,bits,List.range_succ,List.flatMap_append,List.append_assoc]
      rw [he,he,hy]
      have hk' : k<levels φ := hk
      have hfin : (⟨k,hk⟩ : Fin (levels φ)) = ⟨k,hk'⟩ := Fin.ext rfl
      unfold EmitPred at hb
      simpa only [field,dite_eq_left hk',L,hfin] using hb)
  simpa only [machine,w,zs,bits,List.range_zero,List.flatMap_nil,List.append_nil,L,Nat.add_assoc] using h

end UnconstrainedPACDetection.FormulaSwitchTailLevels

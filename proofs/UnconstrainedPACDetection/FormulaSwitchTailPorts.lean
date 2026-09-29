module

public import proofs.UnconstrainedPACDetection.FormulaSwitchTailGate

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchTailPorts
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (tag index)
open FormulaSwitchTailReentrant (frame parked)
open FormulaVertexTailFields (vertex)

theorem inc_hoare (i r a L V C : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    (incRegTM (10 : Fin 21)).HoareTime (EmitPred inp (frame i r a L V C) ys)
      (EmitPred inp (frame i r (a+1) L V C) ys) (2*a+4) := by
  have h := incRegTM_hoareTime (10 : Fin 21) a inp (frame i r a L V C) ys hi
    (fun t _ => parked _ _ _ _ _ _ t) rfl
  have he : Function.update (frame i r a L V C) 10 (regTape (a+1)) = frame i r (a+1) L V C := by
    funext t; fin_cases t <;> simp [frame,FormulaSwitchTailHeads.frame,FormulaChangingFrame.extend,
      FormulaSwitchVariableHeads.bank,FormulaSwitchVariableHeads.extend,
      FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he] at h
  exact h

def machine (right : Bool) (rt : Option Bool) : Nat → TM 21
  | 0 => emitBitsTM []
  | n+1 => seqTM (machine right rt n)
      (if hn : n<20 then seqTM (FormulaSwitchTailGate.machine ⟨n,hn⟩ right rt) (incRegTM 10)
        else emitBitsTM [])

def field (φ : SAT.CNF) (i : Fin (levels φ)) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (p : Nat) : List Bool :=
  if hp : p<20 then vertex φ right r (SwitchStack.sw i ⟨p,hp⟩) else []

def bits (φ : SAT.CNF) (i : Fin (levels φ)) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (n : Nat) : List Bool :=
  (List.range n).flatMap (field φ i right r)

def stepBudget (φ : SAT.CNF) : Nat := FormulaSwitchTailGate.budget φ+40*levels φ+44

theorem hoare (φ : SAT.CNF) (i : Fin (levels φ)) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (n : Nat) (hn : n≤20)
    (ys : List Bool) : (machine right (tag r) n).HoareTime
      (EmitPred (word φ.encode) (frame i.val (index r) (20*i.val) (levels φ) (varCount φ) φ.length) ys)
      (EmitPred (word φ.encode) (frame i.val (index r) (20*i.val+n) (levels φ) (varCount φ) φ.length)
        (ys ++ bits φ i right r n)) (n*stepBudget φ+1) := by
  induction n with
  | zero =>
    unfold EmitPred
    simpa only [machine,bits,List.range_zero,List.flatMap_nil,List.append_nil,Nat.add_zero,Nat.zero_mul,Nat.zero_add]
      using (emitBitsTM_hoareTime [] (word φ.encode) (frame i.val (index r) (20*i.val) (levels φ) (varCount φ) φ.length)
        ys (word_parked _) (parked _ _ _ _ _ _)).mono_bound (show [].length ≤ 1 by decide)
  | succ n ih =>
    have hn' : n<20 := by omega
    have h0 := ih (by omega)
    have h1 := FormulaSwitchTailGate.hoare φ i ⟨n,hn'⟩ right r (ys ++ bits φ i right r n)
    have h2 := inc_hoare i.val (index r) (20*i.val+n) (levels φ) (varCount φ) φ.length
      (word φ.encode) (word_parked _) ((ys ++ bits φ i right r n) ++ vertex φ right r (SwitchStack.sw i ⟨n,hn'⟩))
    have h12 := seqTM_hoareTime _ _ h1 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _) _) h2
    have h := seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _) _) h12
    have hi := i.isLt
    have hb : n*stepBudget φ+1+1+(FormulaSwitchTailGate.budget φ+1+(2*(20*i.val+n)+4)) ≤
        (n+1)*stepBudget φ+1 := by rw [Nat.add_mul]; unfold stepBudget; omega
    simpa only [machine,dite_eq_left hn',bits,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,field,dite_eq_left hn',List.append_assoc,Nat.add_assoc] using h.mono_bound hb

end UnconstrainedPACDetection.FormulaSwitchTailPorts

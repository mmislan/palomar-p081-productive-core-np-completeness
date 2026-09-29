module

public import proofs.UnconstrainedPACDetection.FormulaSwitchVariableHeads
public import proofs.UnconstrainedPACDetection.FormulaSwitchPair

@[expose] public section

namespace UnconstrainedPACDetection.FormulaMergedHeads
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning headMeaning)
open FormulaSwitchVariableHeads (bank parked)

def clauseRoute : Equiv.Perm (Fin 20) where
  toFun := ![0,1,2,3,4,9,10,11,12,13,5,6,7,8,14,15,16,17,18,19]
  invFun := ![0,1,2,3,4,10,11,12,13,5,6,7,8,9,14,15,16,17,18,19]
  left_inv := by intro t; fin_cases t <;> rfl
  right_inv := by intro t; fin_cases t <;> rfl

def clauseQuery (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 20 :=
  VerifierWorkPermutation.machine (placeWorkTM 0 10 (FormulaClausePair.machine p true right plan)) clauseRoute

def clause (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 20 :=
  seqTM (copyIntoTM 18 3) (seqTM (clauseQuery p right plan) (clearRegTM 3))

def field (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (s : Bool) : List Bool :=
  if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ) (a,.inl s)
  then BinaryFields.encodeField (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,.inl s)).bits
  else []

theorem merged_meaning (φ : SAT.CNF) (s : Bool) :
    headMeaning φ (.inl s) = if s then FormulaWiring.sinkQ φ else FormulaWiring.sinkP φ := by
  cases s <;> simp [headMeaning,headVertex,MarkedGraph.decode,FormulaIndexedGraph.terminals,
    PACFormulaReduction.terminals,PACFormulaReduction.terminal]

theorem clause_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (v j f g : Nat) (ys : List Bool) :
    (clause p right (choose right (tag r) (tag a) (some false))).HoareTime
      (EmitPred (word φ.encode) (bank i.val v j (index r) (index a) 0 f (levels φ) (varCount φ) g φ.length) ys)
      (EmitPred (word φ.encode) (bank i.val v j (index r) (index a) 0 f (levels φ) (varCount φ) g φ.length)
        (ys ++ field φ right r a false))
      (2*φ.length^2+15*φ.length+20*φ.encode.length+3*(FormulaIndexedGraph.labels φ).length+143) := by
  let w := bank i.val v j (index r) (index a) 0 f (levels φ) (varCount φ) g φ.length
  let z := Function.update w 3 (regTape φ.length)
  have hp : ∀ t, Parked (w t) := parked _ _ _ _ _ _ _ _ _ _ _
  have hz : ∀ t, Parked (z t) := by
    intro t; by_cases ht : t=3
    · subst t; exact parked_regTape _
    · simpa only [z,Function.update_of_ne ht] using hp t
  have hzero : w 3 = regTape 0 := FormulaEndpointRegisters.unary_word 0
  have h0 := copyIntoTM_hoareTime (18 : Fin 20) 3 (by decide) φ.length 0 (word φ.encode) w ys
    (word_parked _) (fun t _ => hp t) rfl hzero
  have hm : headMeaning φ (.inl false) = FormulaClausePair.toVertex φ i ⟨φ.length,by omega⟩ p true := by
    simpa [FormulaClausePair.toVertex,FormulaWiring.sinkP] using merged_meaning φ false
  have hq := FormulaClausePair.canonical_hoare φ i ⟨φ.length,by omega⟩ p true right r a (.inl false) ha hm ys
  have h1 := FormulaRoutedFrame.hoare _ 0 10 clauseRoute _ _ z _ _ _ hz (by
    intro t; fin_cases t <;> first | rfl | exact FormulaEndpointRegisters.unary_word 0) hq
  have h2 := clearRegTM_hoareTime (3 : Fin 20) φ.length (word φ.encode) z
    (ys ++ field φ right r a false) (word_parked _) (fun t _ => hz t) (by simp [z])
  have he : Function.update z 3 (regTape 0) = w := by
    simp only [z,Function.update_idem,← hzero,Function.update_eq_self]
  rw [he] at h2
  have h12 := seqTM_hoareTime _ _ h1 (emitPred_transition (word_parked _) hz _) h2
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) hz _) h12).mono_bound (by nlinarith)

def switchRoute : Equiv.Perm (Fin 20) where
  toFun := ![0,1,2,8,3,4,7,13,9,10,11,12,19,5,6,14,15,16,17,18]
  invFun := ![0,1,2,4,5,13,14,6,3,8,9,10,11,7,15,16,17,18,19,12]
  left_inv := by intro t; fin_cases t <;> rfl
  right_inv := by intro t; fin_cases t <;> rfl

def switch (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 20 :=
  VerifierWorkPermutation.machine (placeWorkTM 0 7
    (FormulaVariablePair.machine (FormulaSwitchPair.enabled (FormulaSwitchPair.mode p 4))
      (FormulaSwitchPair.offset (FormulaSwitchPair.mode p 4)) false right plan)) switchRoute

theorem not_backward (p : ControlSwitch.V) : FormulaSwitchPair.mode p 4 ≠ .backward := by
  fin_cases p <;> decide

theorem switch_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (v j f g : Nat) (ys : List Bool) :
    (switch p right (choose right (tag r) (tag a) (some true))).HoareTime
      (EmitPred (word φ.encode) (bank i.val v j (index r) (index a) 0 f (levels φ) (varCount φ) g φ.length) ys)
      (EmitPred (word φ.encode) (bank i.val v j (index r) (index a) 0 f (levels φ) (varCount φ) g φ.length)
        (ys ++ field φ right r a true))
      (7*i.val+3*(FormulaIndexedGraph.labels φ).length+103) := by
  have hm : headMeaning φ (.inl true) = SwitchStack.sw ⟨0,FormulaWiring.levels_pos φ⟩ 4 := by
    simpa [FormulaWiring.sinkQ] using merged_meaning φ true
  have h := FormulaSwitchPair.canonical_hoare φ i ⟨0,FormulaWiring.levels_pos φ⟩ p 4 right r a (.inl true) ha hm ys
  simp only [FormulaSwitchPair.first,FormulaSwitchPair.second,ite_eq_right (not_backward p),
    tag,index] at h
  have hr := FormulaRoutedFrame.hoare _ 0 7 switchRoute _ _
    (bank i.val v j (index r) (index a) 0 f (levels φ) (varCount φ) g φ.length) _ _ _
    (parked _ _ _ _ _ _ _ _ _ _ _) (by
      intro t; fin_cases t <;> first | rfl | exact FormulaEndpointRegisters.unary_word 0) h
  apply hr.mono_bound
  have hrb := FormulaCoefficientRound.index_bound r
  have hab := FormulaCoefficientRound.index_bound a
  dsimp only [index] at hrb hab
  cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true,Nat.max_zero] <;> omega

def machine (p : ControlSwitch.V) (right : Bool) (rt ta : Option Bool) : TM 20 :=
  seqTM (clause p right (choose right rt ta (some false)))
    (switch p right (choose right rt ta (some true)))

theorem canonical_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (v j f g : Nat) (ys : List Bool) :
    (machine p right (tag r) (tag a)).HoareTime
      (EmitPred (word φ.encode) (bank i.val v j (index r) (index a) 0 f (levels φ) (varCount φ) g φ.length) ys)
      (EmitPred (word φ.encode) (bank i.val v j (index r) (index a) 0 f (levels φ) (varCount φ) g φ.length)
        (ys ++ field φ right r a false ++ field φ right r a true))
      (2*φ.length^2+15*φ.length+20*φ.encode.length+7*i.val+6*(FormulaIndexedGraph.labels φ).length+247) := by
  have h0 := clause_hoare φ i p right r a ha v j f g ys
  have h1 := switch_hoare φ i p right r a ha v j f g (ys ++ field φ right r a false)
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _ _ _) _) h1).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaMergedHeads

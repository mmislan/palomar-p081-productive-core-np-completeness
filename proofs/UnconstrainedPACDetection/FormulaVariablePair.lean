module

public import proofs.UnconstrainedPACDetection.FormulaEqualityPair

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVariablePair
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaCoefficientPlan (Plan choose tag index)
open FormulaEqualityPair (bank parked)
open FormulaPairExecution (tailMeaning headMeaning)

def machine (enabled off₁ off₂ right : Bool) (p : Plan) : TM 13 :=
  if enabled then FormulaEqualityPair.body off₁ off₂ right p else emitBitsTM []

theorem field_eq {n : Nat} (A : Fin n → Fin n → Prop) [DecidableRel A]
    (T : (Bool ⊕ Bool) ↪ Fin n) (right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal T) :
    (if FiniteMarkedSource.arcPredicate A T (a,b) then BinaryFields.encodeField
      (FormulaCoefficientPlan.value (choose right (tag r) (tag a) (tag b)) (index r)
        (if right then index b else index a)).bits else []) =
    (if FiniteMarkedSource.arcPredicate A T (a,b) then BinaryFields.encodeField
      (FormulaOrderedTable.coefficient T right r (a,b)).bits else []) := by
  by_cases h : FiniteMarkedSource.arcPredicate A T (a,b)
  · have hn := rows_distinct (FromAdjacency.network (MarkedGraph.pulled A T)) ⟨(a,b),h⟩
    have hv := FormulaCoefficientPlan.coefficient_value T right r a b hn
    have hs : index (if right then b else a) = if right then index b else index a := by
      cases right <;> rfl
    rw [hs] at hv
    simp only [ite_eq_left h,hv]
  · simp only [ite_eq_right h]

theorem arc_meaning (φ : SAT.CNF)
    (a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (x y : FormulaWiring.Vertex φ) (ha : tailMeaning φ a = x) (hb : headMeaning φ b = y)
    (hne : x ≠ y) : FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,b) ↔ FormulaWiring.adjacency φ x y := by
  have hd : tailVertex a ≠ headVertex b := by
    intro h
    apply hne
    have he := congrArg (fun q => FormulaIndexedGraph.vertexEquiv φ
      (MarkedGraph.decode (FormulaIndexedGraph.terminals φ) q)) h
    change tailMeaning φ a = headMeaning φ b at he
    simpa only [ha,hb] using he
  change FormulaWiring.adjacency φ (tailMeaning φ a) (headMeaning φ b) ∧
    tailVertex a ≠ headVertex b ↔ _
  rw [ha,hb,and_iff_left hd]

/-- Local execution template; each exported family below proves the guard premise
    directly from the actual formula adjacency definition. -/
theorem canonical (φ : SAT.CNF) (enabled off₁ off₂ right : Bool) (x y z w : Nat)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (hrel : FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,b) ↔
      enabled=true ∧ x+(if off₁ then 1 else 0)=y ∧ z+(if off₂ then 1 else 0)=w)
    (ys : List Bool) :
    (machine enabled off₁ off₂ right (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred (word φ.encode) (bank x y z w (index r) (index a) (index b)) ys)
      (EmitPred (word φ.encode) (bank x y z w (index r) (index a) (index b))
        (ys ++ if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
          (FormulaIndexedGraph.terminals φ) (a,b) then BinaryFields.encodeField
            (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits else []))
      (4*x+4*z+3*max (x+1) y+3*max (z+1) w+
        3*max (index r) (if right then index b else index a)+97) := by
  have hraw : (machine enabled off₁ off₂ right (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred (word φ.encode) (bank x y z w (index r) (index a) (index b)) ys)
      (EmitPred (word φ.encode) (bank x y z w (index r) (index a) (index b))
        (ys ++ if enabled=true ∧ x+(if off₁ then 1 else 0)=y ∧ z+(if off₂ then 1 else 0)=w then
          BinaryFields.encodeField (FormulaCoefficientPlan.value
            (choose right (tag r) (tag a) (tag b)) (index r)
            (if right then index b else index a)).bits else []))
      (4*x+4*z+3*max (x+1) y+3*max (z+1) w+
        3*max (index r) (if right then index b else index a)+97) := by
    cases enabled
    · have h := (emitBitsTM_hoareTime ([] : List Bool) (word φ.encode)
        (bank x y z w (index r) (index a) (index b)) ys (word_parked _) (parked _ _ _ _ _ _ _)).mono_bound
        (show 0 ≤ 4*x+4*z+3*max (x+1) y+3*max (z+1) w+
          3*max (index r) (if right then index b else index a)+97 by omega)
      unfold EmitPred
      simpa only [machine,Bool.false_eq_true,ite_false,false_and,List.append_nil] using h
    · simpa only [machine,Bool.true_eq,ite_true,true_and] using
        FormulaEqualityPair.body_hoare off₁ off₂ right (choose right (tag r) (tag a) (tag b))
          x y z w (index r) (index a) (index b) ys (word φ.encode) (word_parked _)
  simpa only [← hrel,field_eq] using hraw

theorem variable_entry (φ : SAT.CNF) (v : Fin (FormulaWiring.varCount φ+1))
    (w : Fin (FormulaWiring.varCount φ)) (j : Fin (FormulaWiring.levels φ+1)) (s right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = Sum.inr (.var v))
    (hb : headMeaning φ b = Sum.inr (.rail w s j)) (ys : List Bool) :
    (machine true false false right (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred (word φ.encode) (bank v.val w.val j.val 0 (index r) (index a) (index b)) ys)
      (EmitPred (word φ.encode) (bank v.val w.val j.val 0 (index r) (index a) (index b))
        (ys ++ if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
          (FormulaIndexedGraph.terminals φ) (a,b) then BinaryFields.encodeField
            (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits else []))
      (4*v.val+4*j.val+3*max (v.val+1) w.val+3*max (j.val+1) 0+
        3*max (index r) (if right then index b else index a)+97) := by
  apply canonical φ true false false right v.val w.val j.val 0 r a b _ ys
  rw [arc_meaning φ a b _ _ ha hb (by intro h; cases h)]
  change (v.val=w.val ∧ j.val=0) ↔ _
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero,true_and]

theorem variable_exit (φ : SAT.CNF) (v : Fin (FormulaWiring.varCount φ))
    (j : Fin (FormulaWiring.levels φ+1)) (w : Fin (FormulaWiring.varCount φ+1)) (s right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = Sum.inr (.rail v s j))
    (hb : headMeaning φ b = Sum.inr (.var w)) (ys : List Bool) :
    (machine true false true right (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred (word φ.encode) (bank j.val (FormulaWiring.levels φ) v.val w.val (index r) (index a) (index b)) ys)
      (EmitPred (word φ.encode) (bank j.val (FormulaWiring.levels φ) v.val w.val (index r) (index a) (index b))
        (ys ++ if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
          (FormulaIndexedGraph.terminals φ) (a,b) then BinaryFields.encodeField
            (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits else []))
      (4*j.val+4*v.val+3*max (j.val+1) (FormulaWiring.levels φ)+3*max (v.val+1) w.val+
        3*max (index r) (if right then index b else index a)+97) := by
  apply canonical φ true false true right j.val (FormulaWiring.levels φ) v.val w.val r a b _ ys
  rw [arc_meaning φ a b _ _ ha hb (by intro h; cases h)]
  change (j.val=FormulaWiring.levels φ ∧ w.val=v.val+1) ↔ _
  simp only [Bool.false_eq_true,ite_false,ite_true,Nat.add_zero,true_and]
  exact and_congr_right (fun _ => eq_comm)

theorem clause_entry (φ : SAT.CNF) (v : Fin (FormulaWiring.varCount φ+1))
    (c : Fin (φ.length+1)) (right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = Sum.inr (.var v))
    (hb : headMeaning φ b = Sum.inr (.clause c)) (ys : List Bool) :
    (machine true false false right (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred (word φ.encode) (bank v.val (FormulaWiring.varCount φ) c.val 0 (index r) (index a) (index b)) ys)
      (EmitPred (word φ.encode) (bank v.val (FormulaWiring.varCount φ) c.val 0 (index r) (index a) (index b))
        (ys ++ if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
          (FormulaIndexedGraph.terminals φ) (a,b) then BinaryFields.encodeField
            (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits else []))
      (4*v.val+4*c.val+3*max (v.val+1) (FormulaWiring.varCount φ)+3*max (c.val+1) 0+
        3*max (index r) (if right then index b else index a)+97) := by
  apply canonical φ true false false right v.val (FormulaWiring.varCount φ) c.val 0 r a b _ ys
  rw [arc_meaning φ a b _ _ ha hb (by intro h; cases h)]
  change (v.val=FormulaWiring.varCount φ ∧ c.val=0) ↔ _
  simp only [Bool.false_eq_true,ite_false,Nat.add_zero,true_and]

theorem last_switch (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (port : ControlSwitch.V) (v : Fin (FormulaWiring.varCount φ+1)) (right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i port)
    (hb : headMeaning φ b = Sum.inr (.var v)) (ys : List Bool) :
    (machine (decide (port=5)) true false right (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred (word φ.encode) (bank i.val (FormulaWiring.levels φ) v.val 0 (index r) (index a) (index b)) ys)
      (EmitPred (word φ.encode) (bank i.val (FormulaWiring.levels φ) v.val 0 (index r) (index a) (index b))
        (ys ++ if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
          (FormulaIndexedGraph.terminals φ) (a,b) then BinaryFields.encodeField
            (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits else []))
      (4*i.val+4*v.val+3*max (i.val+1) (FormulaWiring.levels φ)+3*max (v.val+1) 0+
        3*max (index r) (if right then index b else index a)+97) := by
  apply canonical φ (decide (port=5)) true false right i.val (FormulaWiring.levels φ) v.val 0 r a b _ ys
  rw [arc_meaning φ a b _ _ ha hb (by intro h; cases h)]
  change (((port=5 ∧ i.val+1=FormulaWiring.levels φ) ∨ port=6 ∨ port=7) ∧
      port=5 ∧ i.val+1=FormulaWiring.levels φ ∧ v.val=0) ↔ _
  simp only [decide_eq_true_eq,ite_true,Bool.false_eq_true,ite_false,Nat.add_zero]
  aesop

end UnconstrainedPACDetection.FormulaVariablePair

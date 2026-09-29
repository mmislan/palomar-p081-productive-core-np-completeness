module

public import proofs.UnconstrainedPACDetection.FormulaPairExecution
public import proofs.Complexitylib.Models.TuringMachine.Registers.DecReg

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchRailPair
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaCoefficientPlan (Plan choose tag index)
open FormulaPairExecution (bank parked comparison comparison_hoare blocking blocking_hoare
  coefficient coefficient_hoare tailMeaning headMeaning)

theorem increment_hoare (i v j r a b : Nat) (ys : List Bool) (inp : Tape)
    (hi : Parked inp) : (incRegTM (0 : Fin 14)).HoareTime
    (EmitPred inp (bank i v j r a b) ys)
    (EmitPred inp (bank (i+1) v j r a b) ys) (2*i+4) := by
  have h := incRegTM_hoareTime (0 : Fin 14) i inp (bank i v j r a b) ys hi
    (fun t _ => parked i v j r a b t) rfl
  have he : Function.update (bank i v j r a b) 0 (regTape (i+1)) =
      bank (i+1) v j r a b := by
    funext t; fin_cases t <;> simp [bank]
  rw [he] at h
  exact h

theorem decrement_hoare (i v j r a b : Nat) (ys : List Bool) (inp : Tape)
    (hi : Parked inp) : (decRegTM (0 : Fin 14)).HoareTime
    (EmitPred inp (bank (i+1) v j r a b) ys)
    (EmitPred inp (bank i v j r a b) ys) (2*i+6) := by
  have h := decRegTM_hoareTime (0 : Fin 14) (i+1) inp (bank (i+1) v j r a b) ys hi
    (fun t _ => parked (i+1) v j r a b t) rfl
  have he : Function.update (bank (i+1) v j r a b) 0 (regTape (i+1-1)) =
      bank i v j r a b := by
    funext t; fin_cases t <;> simp [bank]
  rw [he] at h
  exact h.mono_bound (by omega)

def offsetComparison : TM 14 := seqTM (incRegTM 0) (seqTM comparison (decRegTM 0))

theorem offset_hoare (i v j r a b : Nat) (ys : List Bool) (inp : Tape) (hi : Parked inp) :
    offsetComparison.HoareTime (EmitPred inp (bank i v j r a b) ys)
      (EmitPred inp (bank i v j r a b) (ys ++ [decide (i+1=j)]))
      (4*i+3*max (i+1) j+32) := by
  have h2 := seqTM_hoareTime _ _ (comparison_hoare (i+1) v j r a b ys inp hi)
    (emitPred_transition hi (parked _ _ _ _ _ _) _)
    (decrement_hoare i v j r a b (ys ++ [decide (i+1=j)]) inp hi)
  have h := seqTM_hoareTime _ _ (increment_hoare i v j r a b ys inp hi)
    (emitPred_transition hi (parked _ _ _ _ _ _) _) h2
  exact h.mono_bound (by omega)

def body (s right : Bool) (p : Plan) : TM 14 :=
  seqTM offsetComparison (FormulaCoefficientGate.gate
    (seqTM (blocking s) (FormulaCoefficientGate.gate (coefficient right p))))

theorem body_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (j r a b : Nat) (s right : Bool)
    (p : Plan) (ys : List Bool) :
    (body s right p).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val j r a b) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j r a b)
        (ys ++ if i.val+1 = j ∧ FormulaWiring.blocked φ i v s = true then
          BinaryFields.encodeField
            (FormulaCoefficientPlan.value p r (if right then b else a)).bits else []))
      (24*φ.encode.length+26*v.val+4*i.val+3*max (i.val+1) j+
        3*max r (if right then b else a)+252) := by
  have hi := word_parked φ.encode
  have hp := parked i.val v.val j r a b
  have hc := coefficient_hoare right p i.val v.val j r a b ys _ hi
  have hg := FormulaCoefficientGate.gate_hoare _ (FormulaWiring.blocked φ i v s)
    _ _ ys _ _ hi hp hc
  have hb := seqTM_hoareTime _ _ (blocking_hoare φ i v j r a b s ys)
    (emitPred_transition hi hp _) hg
  have ho := FormulaCoefficientGate.gate_hoare _ (decide (i.val+1=j)) _ _ ys _ _ hi hp hb
  have h := seqTM_hoareTime _ _ (offset_hoare i.val v.val j r a b ys _ hi)
    (emitPred_transition hi hp _) ho
  have h' := h.mono_bound (show (4*i.val+3*max (i.val+1) j+32)+1+
      ((24*φ.encode.length+26*v.val+187)+1+
        (3*max r (if right then b else a)+27+2)+2) ≤
      24*φ.encode.length+26*v.val+4*i.val+3*max (i.val+1) j+
        3*max r (if right then b else a)+252 by omega)
  by_cases hij : i.val+1=j <;> cases hz : FormulaWiring.blocked φ i v s <;>
    simpa [body,hij,hz] using h'

def machine (port : ControlSwitch.V) (s right : Bool) (p : Plan) : TM 14 :=
  if port = 7 then body s right p else emitBitsTM []

theorem adjacency_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (j : Fin (FormulaWiring.levels φ+1))
    (port : ControlSwitch.V) (r a b : Nat) (s right : Bool) (p : Plan) (ys : List Bool) :
    (machine port s right p).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val j.val r a b) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j.val r a b)
        (ys ++ if FormulaWiring.adjacency φ (SwitchStack.sw i port) (Sum.inr (.rail v s j))
          then BinaryFields.encodeField
            (FormulaCoefficientPlan.value p r (if right then b else a)).bits else []))
      (24*φ.encode.length+26*v.val+4*i.val+3*max (i.val+1) j.val+
        3*max r (if right then b else a)+252) := by
  by_cases ha : port = 7
  · subst port
    have he : FormulaWiring.adjacency φ (SwitchStack.sw i 7) (Sum.inr (.rail v s j)) ↔
        i.val+1 = j.val ∧ FormulaWiring.blocked φ i v s = true := by
      change (((7 : ControlSwitch.V) = 5 ∧ i.val+1 = FormulaWiring.levels φ) ∨
        7 = 6 ∨ 7 = 7) ∧ 7 = 7 ∧ j.val = i.val+1 ∧
        FormulaWiring.blocked φ i v s = true ↔ _
      simp only [or_true,true_and]
      exact and_congr_left (fun _ => eq_comm)
    simpa only [machine,ite_eq_left rfl,he,ite_true] using
      body_hoare φ i v j.val r a b s right p ys
  · have hn : ¬FormulaWiring.adjacency φ (SwitchStack.sw i port) (Sum.inr (.rail v s j)) :=
      fun he => ha he.2.1
    have h := (emitBitsTM_hoareTime ([] : List Bool) (word φ.encode)
      (bank i.val v.val j.val r a b) ys (word_parked _) (parked _ _ _ _ _ _)).mono_bound
      (show 0 ≤ 24*φ.encode.length+26*v.val+4*i.val+3*max (i.val+1) j.val+
        3*max r (if right then b else a)+252 by omega)
    unfold EmitPred
    simpa only [machine,ite_eq_right ha,ite_eq_right hn,List.append_nil] using h

theorem canonical_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (j : Fin (FormulaWiring.levels φ+1))
    (port : ControlSwitch.V) (s right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i port)
    (hb : headMeaning φ b = Sum.inr (.rail v s j)) (ys : List Bool) :
    (machine port s right (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val j.val (index r) (index a) (index b)) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j.val (index r) (index a) (index b))
        (ys ++ if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
            (FormulaIndexedGraph.terminals φ) (a,b) then
          BinaryFields.encodeField (FormulaOrderedTable.coefficient
            (FormulaIndexedGraph.terminals φ) right r (a,b)).bits else []))
      (24*φ.encode.length+26*v.val+4*i.val+3*max (i.val+1) j.val+
        3*(FormulaIndexedGraph.labels φ).length+252) := by
  have hd : tailVertex a ≠ headVertex b := by
    intro he
    have hh := congrArg (fun x => FormulaIndexedGraph.vertexEquiv φ
      (MarkedGraph.decode (FormulaIndexedGraph.terminals φ) x)) he
    change tailMeaning φ a = headMeaning φ b at hh
    rw [ha,hb] at hh
    cases hh
  have he : FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,b) ↔
      FormulaWiring.adjacency φ (SwitchStack.sw i port) (Sum.inr (.rail v s j)) := by
    change FormulaWiring.adjacency φ (tailMeaning φ a) (headMeaning φ b) ∧
      tailVertex a ≠ headVertex b ↔ _
    rw [ha,hb,and_iff_left hd]
  have h := adjacency_hoare φ i v j port (index r) (index a) (index b) s right
    (choose right (tag r) (tag a) (tag b)) ys
  have hr := FormulaCoefficientRound.index_bound r
  have hat := FormulaCoefficientRound.index_bound a
  have hbt := FormulaCoefficientRound.index_bound b
  have h' := h.mono_bound (show 24*φ.encode.length+26*v.val+4*i.val+3*max (i.val+1) j.val+
      3*max (index r) (if right then index b else index a)+252 ≤
      24*φ.encode.length+26*v.val+4*i.val+3*max (i.val+1) j.val+
        3*(FormulaIndexedGraph.labels φ).length+252 by
    cases right <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega)
  by_cases hadj : FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,b)
  · have hn := rows_distinct (FromAdjacency.network (MarkedGraph.pulled
      (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ))) ⟨(a,b),hadj⟩
    have hv := FormulaCoefficientPlan.coefficient_value (FormulaIndexedGraph.terminals φ)
      right r a b hn
    have hs : index (if right then b else a) = if right then index b else index a := by
      cases right <;> rfl
    rw [hs] at hv
    simpa only [← he,ite_eq_left hadj,hv] using h'
  · simpa only [← he,ite_eq_right hadj] using h'

end UnconstrainedPACDetection.FormulaSwitchRailPair

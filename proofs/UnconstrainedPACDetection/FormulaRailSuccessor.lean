module

public import proofs.UnconstrainedPACDetection.FormulaSwitchRailPair
public import proofs.UnconstrainedPACDetection.FormulaNegativeGate
public import proofs.UnconstrainedPACDetection.FormulaRoutedFrame

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailSuccessor
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaCoefficientPlan (Plan choose tag index)
open FormulaPairExecution (place_hoare tailMeaning headMeaning)

def bank (i v j r a b w : Nat) : Fin 15 → Tape :=
  ![regTape i,word [],word [],word [],word [],regTape v,regTape j,word [],word [true],
    regTape r,regTape a,regTape b,word [],word [true],regTape w]

theorem parked (i v j r a b w : Nat) : ∀ t, Parked (bank i v j r a b w t) := by
  intro t; fin_cases t
  all_goals first | exact parked_regTape _ | exact word_parked _

def permutation : Equiv.Perm (Fin 15) :=
  (((Equiv.swap 0 5).trans (Equiv.swap 1 14)).trans (Equiv.swap 2 7)).trans (Equiv.swap 3 8)

def variableTest : TM 15 := VerifierWorkPermutation.machine
  (placeWorkTM 0 11 FormulaClauseCompare.machine) permutation

theorem variableTest_hoare (i v j r a b w : Nat) (ys : List Bool) (inp : Tape)
    (hi : Parked inp) : variableTest.HoareTime
    (EmitPred inp (bank i v j r a b w) ys)
    (EmitPred inp (bank i v j r a b w) (ys ++ [decide (v=w)])) (3*max v w+20) := by
  have hc := FormulaClauseCompare.compare_hoare v w [true] ys inp hi
  simp only [List.isEmpty_cons,Bool.not_false,Bool.and_true] at hc
  apply FormulaRoutedFrame.hoare _ 0 11 _ _ _ _ _ _ _ (parked i v j r a b w) _ hc
  intro t; fin_cases t <;>
    simp [permutation,Equiv.trans_apply,Equiv.swap_apply_def,placeWorkIdx,bank,FormulaClauseCompare.bank]

theorem lift {M : TM 14} (i v j r a b w : Nat) (inp : Tape) (ys zs : List Bool) (B : Nat)
    (h : M.HoareTime (EmitPred inp (FormulaPairExecution.bank i v j r a b) ys)
      (EmitPred inp (FormulaPairExecution.bank i v j r a b) zs) B) :
    (placeWorkTM 0 1 M).HoareTime (EmitPred inp (bank i v j r a b w) ys)
      (EmitPred inp (bank i v j r a b w) zs) B := by
  apply place_hoare _ 0 1 _ _ _ _ _ _ (parked i v j r a b w) _ h
  intro t; fin_cases t <;> rfl

def body (s right : Bool) (p : Plan) : TM 15 :=
  seqTM variableTest (FormulaCoefficientGate.gate
    (seqTM (placeWorkTM 0 1 FormulaSwitchRailPair.offsetComparison)
      (FormulaCoefficientGate.gate
        (seqTM (placeWorkTM 0 1 (FormulaPairExecution.blocking s))
          (FormulaNegativeGate.gate (placeWorkTM 0 1 (FormulaPairExecution.coefficient right p)))))))

theorem body_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (j r a b w : Nat) (s right : Bool)
    (p : Plan) (ys : List Bool) :
    (body s right p).HoareTime (EmitPred (word φ.encode) (bank i.val v.val j r a b w) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j r a b w)
        (ys ++ if v.val=w ∧ i.val+1=j ∧ FormulaWiring.blocked φ i v s = false then
          BinaryFields.encodeField (FormulaCoefficientPlan.value p r (if right then b else a)).bits else []))
      (24*φ.encode.length+26*v.val+3*max v.val w+4*i.val+3*max (i.val+1) j+
        3*max r (if right then b else a)+275) := by
  have hi := word_parked φ.encode
  have hp := parked i.val v.val j r a b w
  have hc := lift i.val v.val j r a b w _ _ _ _
    (FormulaPairExecution.coefficient_hoare right p i.val v.val j r a b ys _ hi)
  have hg := FormulaNegativeGate.gate_hoare _ (FormulaWiring.blocked φ i v s)
    _ _ ys _ _ hi hp hc
  have hb := seqTM_hoareTime _ _
    (lift i.val v.val j r a b w _ _ _ _ (FormulaPairExecution.blocking_hoare φ i v j r a b s ys))
    (emitPred_transition hi hp _) hg
  have hgb := FormulaCoefficientGate.gate_hoare _ (decide (i.val+1=j)) _ _ ys _ _ hi hp hb
  have ho := seqTM_hoareTime _ _ (lift i.val v.val j r a b w _ _ _ _
      (FormulaSwitchRailPair.offset_hoare i.val v.val j r a b ys _ hi))
    (emitPred_transition hi hp _) hgb
  have hgo := FormulaCoefficientGate.gate_hoare _ (decide (v.val=w)) _ _ ys _ _ hi hp ho
  have h := seqTM_hoareTime _ _ (variableTest_hoare i.val v.val j r a b w ys _ hi)
    (emitPred_transition hi hp _) hgo
  have h' := h.mono_bound (show (3*max v.val w+20)+1+
      ((4*i.val+3*max (i.val+1) j+32)+1+
        ((24*φ.encode.length+26*v.val+187)+1+
          (3*max r (if right then b else a)+27+2)+2)+2) ≤
      24*φ.encode.length+26*v.val+3*max v.val w+4*i.val+3*max (i.val+1) j+
        3*max r (if right then b else a)+275 by omega)
  by_cases hv : v.val=w <;> by_cases hj : i.val+1=j <;>
    cases hz : FormulaWiring.blocked φ i v s <;> simpa [body,hv,hj,hz] using h'

def machine (ended s t right : Bool) (p : Plan) : TM 15 :=
  if ended || (s != t) then emitBitsTM [] else body s right p

theorem adjacency_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v w : Fin (FormulaWiring.varCount φ)) (j : Fin (FormulaWiring.levels φ+1))
    (r a b : Nat) (s t right : Bool) (p : Plan) (ys : List Bool) :
    (machine false s t right p).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val j.val r a b w.val) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j.val r a b w.val)
        (ys ++ if FormulaWiring.adjacency φ
            (Sum.inr (.rail v s ⟨i.val,by omega⟩)) (Sum.inr (.rail w t j)) then
          BinaryFields.encodeField (FormulaCoefficientPlan.value p r (if right then b else a)).bits else []))
      (24*φ.encode.length+26*v.val+3*max v.val w.val+4*i.val+3*max (i.val+1) j.val+
        3*max r (if right then b else a)+275) := by
  have he : FormulaWiring.adjacency φ
      (Sum.inr (.rail v s ⟨i.val,by omega⟩)) (Sum.inr (.rail w t j)) ↔
      s=t ∧ v.val=w.val ∧ i.val+1=j.val ∧ FormulaWiring.blocked φ i v s = false := by
    change (v=w ∧ s=t ∧ ∃ h : i.val < FormulaWiring.levels φ,
      j.val=i.val+1 ∧ FormulaWiring.blocked φ ⟨i.val,h⟩ v s = false) ↔ _
    simp only [Fin.mk_val]
    constructor
    · rintro ⟨hv,hs,_,hj,hb⟩; exact ⟨hs,congrArg Fin.val hv,hj.symm,hb⟩
    · rintro ⟨hs,hv,hj,hb⟩; exact ⟨Fin.ext hv,hs,i.isLt,hj.symm,hb⟩
  by_cases hst : s=t
  · subst t
    simpa only [he,machine,bne_self_eq_false,Bool.or_false,Bool.false_eq_true,ite_false,
      true_and] using body_hoare φ i v j.val r a b w.val s right p ys
  · have hn : ¬FormulaWiring.adjacency φ
        (Sum.inr (.rail v s ⟨i.val,by omega⟩)) (Sum.inr (.rail w t j)) := fun h => hst (he.mp h).1
    have h := (emitBitsTM_hoareTime ([] : List Bool) (word φ.encode)
      (bank i.val v.val j.val r a b w.val) ys (word_parked _) (parked _ _ _ _ _ _ _)).mono_bound
      (show 0 ≤ 24*φ.encode.length+26*v.val+3*max v.val w.val+4*i.val+
        3*max (i.val+1) j.val+3*max r (if right then b else a)+275 by omega)
    unfold EmitPred
    simpa [machine,hst,hn] using h

theorem canonical_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v w : Fin (FormulaWiring.varCount φ)) (j : Fin (FormulaWiring.levels φ+1))
    (s t right : Bool) (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = Sum.inr (.rail v s ⟨i.val,by omega⟩))
    (hb : headMeaning φ b = Sum.inr (.rail w t j)) (ys : List Bool) :
    (machine false s t right (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val j.val (index r) (index a) (index b) w.val) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j.val (index r) (index a) (index b) w.val)
        (ys ++ if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
            (FormulaIndexedGraph.terminals φ) (a,b) then BinaryFields.encodeField
          (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits else []))
      (24*φ.encode.length+26*v.val+3*max v.val w.val+4*i.val+3*max (i.val+1) j.val+
        3*(FormulaIndexedGraph.labels φ).length+275) := by
  have hd (h : FormulaWiring.adjacency φ
      (Sum.inr (.rail v s ⟨i.val,by omega⟩)) (Sum.inr (.rail w t j))) :
      tailVertex a ≠ headVertex b := by
    intro he
    have hh := congrArg (fun x => FormulaIndexedGraph.vertexEquiv φ
      (MarkedGraph.decode (FormulaIndexedGraph.terminals φ) x)) he
    change tailMeaning φ a = headMeaning φ b at hh
    rw [ha,hb] at hh
    have hj := congrArg Fin.val (FormulaWiring.External.rail.inj (Sum.inr.inj hh)).2.2
    change v=w ∧ s=t ∧ ∃ h : i.val < FormulaWiring.levels φ,
      j.val=i.val+1 ∧ FormulaWiring.blocked φ ⟨i.val,h⟩ v s = false at h
    obtain ⟨_,_,_,hk,_⟩ := h
    change i.val = j.val at hj
    change j.val = i.val+1 at hk
    omega
  have he : FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,b) ↔ FormulaWiring.adjacency φ
      (Sum.inr (.rail v s ⟨i.val,by omega⟩)) (Sum.inr (.rail w t j)) := by
    change FormulaWiring.adjacency φ (tailMeaning φ a) (headMeaning φ b) ∧
      tailVertex a ≠ headVertex b ↔ _
    rw [ha,hb]
    exact ⟨And.left,fun h => ⟨h,hd h⟩⟩
  have h := adjacency_hoare φ i v w j (index r) (index a) (index b) s t right
    (choose right (tag r) (tag a) (tag b)) ys
  have hr := FormulaCoefficientRound.index_bound r
  have hat := FormulaCoefficientRound.index_bound a
  have hbt := FormulaCoefficientRound.index_bound b
  have h' := h.mono_bound (show 24*φ.encode.length+26*v.val+3*max v.val w.val+4*i.val+
      3*max (i.val+1) j.val+3*max (index r) (if right then index b else index a)+275 ≤
      24*φ.encode.length+26*v.val+3*max v.val w.val+4*i.val+3*max (i.val+1) j.val+
        3*(FormulaIndexedGraph.labels φ).length+275 by
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

theorem terminal_cursor_hoare (φ : SAT.CNF) (v w : Fin (FormulaWiring.varCount φ))
    (j : Fin (FormulaWiring.levels φ+1)) (s t right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = Sum.inr (.rail v s ⟨FormulaWiring.levels φ,by omega⟩))
    (hb : headMeaning φ b = Sum.inr (.rail w t j)) (ys : List Bool) :
    (machine true s t right (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred (word φ.encode) (bank (FormulaWiring.levels φ) v.val j.val (index r) (index a) (index b) w.val) ys)
      (EmitPred (word φ.encode) (bank (FormulaWiring.levels φ) v.val j.val (index r) (index a) (index b) w.val)
        (ys ++ if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
            (FormulaIndexedGraph.terminals φ) (a,b) then BinaryFields.encodeField
          (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits else [])) 0 := by
  have hn : ¬FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,b) := by
    intro h
    have h' := h.1
    change FormulaWiring.adjacency φ (tailMeaning φ a) (headMeaning φ b) at h'
    rw [ha,hb] at h'
    exact (Nat.lt_irrefl _ h'.2.2.choose)
  unfold EmitPred
  simpa only [machine,Bool.true_or,Bool.true_eq,ite_true,ite_eq_right hn,
    List.append_nil,List.length_nil] using
    emitBitsTM_hoareTime ([] : List Bool) (word φ.encode)
      (bank (FormulaWiring.levels φ) v.val j.val (index r) (index a) (index b) w.val)
      ys (word_parked _) (parked _ _ _ _ _ _ _)

end UnconstrainedPACDetection.FormulaRailSuccessor

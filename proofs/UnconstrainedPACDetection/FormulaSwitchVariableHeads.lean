module

public import proofs.UnconstrainedPACDetection.FormulaVariableCursor
public import proofs.UnconstrainedPACDetection.FormulaRailClauseHeads

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchVariableHeads
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)

def extend (w : Fin 19 → Tape) (t : Fin 20) : Tape :=
  if h : t.val < 19 then w ⟨t.val,h⟩ else word [true]

theorem extend_parked (w : Fin 19 → Tape) (hp : ∀ t, Parked (w t)) :
    ∀ t, Parked (extend w t) := by
  intro t; unfold extend; split
  · exact hp _
  · exact word_parked _

theorem lift_hoare (m : TM 19) (inp : Tape) (w z : Fin 19 → Tape)
    (ys zs : List Bool) (B : Nat) (hp : ∀ t, Parked (w t))
    (h : m.HoareTime (EmitPred inp w ys) (EmitPred inp z zs) B) :
    (placeWorkTM 0 1 m).HoareTime
      (EmitPred inp (extend w) ys) (EmitPred inp (extend z) zs) B := by
  rintro i work out ⟨rfl,rfl,ho⟩
  obtain ⟨d,t,ht,hr,hh,hi,hw,hout⟩ := h _ _ out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal m 0 1 (extend w) hr
    (by intro q _; exact (extend_parked w hp q).read_ne_start)
  refine ⟨placeWorkCfg m 0 1 (extend w) d,t,ht,?_,hh,hi,?_,hout⟩
  · convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext q; fin_cases q <;> simp [placeWorkCfg,placeWorkInMiddle,extend] <;> rfl
    · rfl
  · funext q; fin_cases q <;> simp [placeWorkCfg,placeWorkInMiddle,extend,hw] <;> rfl

def bank (i v j r a b f L V g C : Nat) : Fin 20 → Tape :=
  extend (FormulaRailClauseHeads.extend (FormulaAllRailHeads.raw i v j r a b f L V g) C)

theorem parked (i v j r a b f L V g C : Nat) : ∀ t, Parked (bank i v j r a b f L V g C t) :=
  extend_parked _ (FormulaRailClauseHeads.extend_parked _ _ (FormulaAllRailHeads.parked _ _ _ _ _ _ _ _ _ _))

def route : Equiv.Perm (Fin 20) where
  toFun := ![0,15,2,8,5,1,7,13,9,10,11,4,19,3,6,12,14,16,17,18]
  invFun := ![0,5,2,13,11,4,14,6,3,8,9,10,15,7,16,1,17,18,19,12]
  left_inv := by intro t; fin_cases t <;> rfl
  right_inv := by intro t; fin_cases t <;> rfl

def round (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 20 :=
  VerifierWorkPermutation.machine
    (placeWorkTM 0 7 (FormulaVariablePair.machine (decide (p=5)) true false right plan)) route

def field (φ : SAT.CNF) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (v : Fin (varCount φ+1)) : List Bool :=
  if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,FormulaVariableCursor.port φ v)
  then BinaryFields.encodeField (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ)
      right r (a,FormulaVariableCursor.port φ v)).bits else []

theorem nonzero_field (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (v : Fin (varCount φ+1)) (hv : v.val ≠ 0) :
    field φ right r a v = [] := by
  exact ite_eq_right (FormulaVariableCursor.nonzero_rejected φ i p a ha v hv)

/-- Exact ordered compression, not just an outdegree assertion. -/
theorem all_variable_fields (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) :
    (List.finRange (varCount φ+1)).flatMap (field φ right r a) = field φ right r a 0 := by
  rw [List.finRange_succ,List.flatMap_cons,List.flatMap_map]
  have hnil : (List.finRange (varCount φ)).flatMap (fun v => field φ right r a v.succ) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro v _
    exact nonzero_field φ i p right r a ha v.succ (by simp)
  simp only [hnil,List.append_nil]

theorem round_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (j f g : Nat) (ys : List Bool) :
    (round p right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i.val 0 j (index r) (index a) (20*levels φ) f (levels φ) (varCount φ) g φ.length) ys)
      (EmitPred (word φ.encode) (bank i.val 0 j (index r) (index a) (20*levels φ) f (levels φ) (varCount φ) g φ.length)
        (ys ++ field φ right r a 0))
      (4*i.val+3*levels φ+3*(FormulaIndexedGraph.labels φ).length+100) := by
  let b := FormulaVariableCursor.port φ 0
  have hb : index b = 20*levels φ := by simpa using FormulaVariableCursor.port_index φ 0
  have ht : tag b = none := rfl
  have h := FormulaVariablePair.last_switch φ i p 0 right r a b ha (FormulaVariableCursor.port_meaning φ 0) ys
  rw [hb,ht] at h
  have h' := FormulaRoutedFrame.hoare _ 0 7 route _ _
    (bank i.val 0 j (index r) (index a) (20*levels φ) f (levels φ) (varCount φ) g φ.length) _ _ _
    (parked _ _ _ _ _ _ _ _ _ _ _) (by
      intro t; fin_cases t <;> first | rfl | exact FormulaEndpointRegisters.unary_word 0) h
  apply h'.mono_bound
  have hi := i.isLt
  have hr := FormulaCoefficientRound.index_bound r
  have ha' := FormulaCoefficientRound.index_bound a
  have hb' := FormulaCoefficientRound.index_bound b
  rw [hb] at hb'
  cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true,Fin.val_zero,
    Nat.mul_zero,Nat.zero_add,Nat.max_eq_right (by omega : i.val+1 ≤ levels φ)] <;> omega

def machine (p : ControlSwitch.V) (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 20 :=
  seqTM (clearRegTM 5) (seqTM (round p right plan)
    (placeWorkTM 0 1 (FormulaRailClauseHeads.machine p right plan)))

/-- The variable-zero check is physically followed by the complete rail/clause stage. -/
theorem canonical_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (p : ControlSwitch.V) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i p) (v j f g : Nat) (ys : List Bool)
    (hj : j ≤ 100*(φ.encode.length+2)^2) (hf : f ≤ 100*(φ.encode.length+2)^2)
    (hg : g ≤ 100*(φ.encode.length+2)^2) :
    (machine p right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i.val v j (index r) (index a) (20*levels φ) f (levels φ) (varCount φ) g φ.length) ys)
      (EmitPred (word φ.encode)
        (extend (FormulaClauseHeadLoop.bank i.val φ.length (index r) (index a)
          (FormulaClauseCursor.base φ+φ.length) (levels φ) (varCount φ) φ.length (regTape φ.length)))
        (ys ++ field φ right r a 0 ++ FormulaRailHeadVariables.bits φ right r a (varCount φ) ++
          FormulaClauseHeadLoop.bits φ right r a φ.length))
      (2*v+4*i.val+3*levels φ+3*(FormulaIndexedGraph.labels φ).length+
        FormulaRailClauseHeads.budget φ+106) := by
  have h0 := clearRegTM_hoareTime (5 : Fin 20) v (word φ.encode)
    (bank i.val v j (index r) (index a) (20*levels φ) f (levels φ) (varCount φ) g φ.length) ys
    (word_parked _) (fun t _ => parked _ _ _ _ _ _ _ _ _ _ _ t) rfl
  have he : Function.update (bank i.val v j (index r) (index a) (20*levels φ) f (levels φ) (varCount φ) g φ.length) 5 (regTape 0) =
      bank i.val 0 j (index r) (index a) (20*levels φ) f (levels φ) (varCount φ) g φ.length := by
    funext t; fin_cases t <;> simp [bank,extend,FormulaRailClauseHeads.extend,FormulaAllRailHeads.raw,
      FormulaRailHeadVariables.extend,FormulaRailHeadPrepare.bank]
  rw [he] at h0
  have h1 := round_hoare φ i p right r a ha j f g ys
  have hL := (FormulaEnumeration.parameter_bounds φ).1
  have h2 := FormulaRailClauseHeads.canonical_hoare φ i p right r a ha 0 j (20*levels φ) f g
    (ys ++ field φ right r a 0) (Nat.zero_le _) hj (by nlinarith) hf hg
  have h2' := lift_hoare _ _ _ _ _ _ _
    (FormulaRailClauseHeads.extend_parked _ _ (FormulaAllRailHeads.parked _ _ _ _ _ _ _ _ _ _)) h2
  have h12 := seqTM_hoareTime _ _ h1 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _ _ _) _) h2'
  exact (seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _ _ _) _) h12).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaSwitchVariableHeads

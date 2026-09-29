module

public import proofs.UnconstrainedPACDetection.FormulaRailSwitchFilter

@[expose] public section

namespace UnconstrainedPACDetection.FormulaPairExecution
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaCoefficientPlan (Plan choose tag index)

/-- Placement preserves any parked caller frame, including populated counters. -/
theorem place_hoare {n : Nat} (M : TM n) (pre post : Nat)
    (inp : Tape) (small : Fin n → Tape) (large : Fin (pre+n+post) → Tape)
    (ys zs : List Bool) (B : Nat)
    (hp : ∀ j, Parked (large j))
    (hm : ∀ j, large (placeWorkIdx pre post j) = small j)
    (h : M.HoareTime (EmitPred inp small ys) (EmitPred inp small zs) B) :
    (placeWorkTM pre post M).HoareTime (EmitPred inp large ys)
      (EmitPred inp large zs) B := by
  rintro i w out ⟨hi,hw,ho⟩
  subst i; subst w
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := h inp small out ⟨rfl,rfl,ho⟩
  have he (c : Cfg n M.Q) (hc : c.work = small) :
      (placeWorkCfg M pre post large c).work = large := by
    funext j
    simp only [placeWorkCfg]
    split
    next hj =>
      rw [hc, ← hm]
      rw [placeWorkIdx_placeWorkCoord]
    next => rfl
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal M pre post large hr
    (by intro j _; exact (hp j).read_ne_start)
  refine ⟨placeWorkCfg M pre post large d,t,ht,?_,hh,hdi,he d hdw,hdo⟩
  convert hs using 1
  apply Cfg.ext
  · rfl
  · rfl
  · exact (he _ rfl).symm
  · rfl

/-- Nine query tapes and five coefficient tapes; all indices are runtime data. -/
def bank (i v j r a b : Nat) : Fin 14 → Tape :=
  ![regTape i,word [],word [],word [],word [],regTape v,regTape j,word [],word [true],
    regTape r,regTape a,regTape b,word [],word [true]]

theorem parked (i v j r a b : Nat) : ∀ t, Parked (bank i v j r a b t) := by
  intro t; fin_cases t
  all_goals first | exact parked_regTape _ | exact word_parked _

def comparison : TM 14 := placeWorkTM 0 5 FormulaRailSwitchFilter.comparison
def blocking (b : Bool) : TM 14 := placeWorkTM 0 5 (FormulaRailSwitchFilter.blocking b)
def coefficient (right : Bool) (p : Plan) : TM 14 :=
  placeWorkTM 9 0 (FormulaCoefficientRound.machine right p)

theorem comparison_hoare (i v j r a b : Nat) (ys : List Bool) (inp : Tape)
    (hi : Parked inp) : comparison.HoareTime
    (EmitPred inp (bank i v j r a b) ys)
    (EmitPred inp (bank i v j r a b) (ys ++ [decide (i=j)])) (3*max i j+20) := by
  apply place_hoare _ 0 5 _ _ _ _ _ _ (parked i v j r a b)
    _ (FormulaRailSwitchFilter.comparison_hoare i v j ys inp hi)
  intro t; fin_cases t <;> rfl

theorem blocking_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (j r a b : Nat) (s : Bool) (ys : List Bool) :
    (blocking s).HoareTime (EmitPred (word φ.encode) (bank i.val v.val j r a b) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j r a b)
        (ys ++ [FormulaWiring.blocked φ i v s])) (24*φ.encode.length+26*v.val+187) := by
  apply place_hoare _ 0 5 _ _ _ _ _ _ (parked i.val v.val j r a b)
    _ (FormulaRailSwitchFilter.blocking_hoare φ i v j s ys)
  intro t; fin_cases t <;> rfl

theorem coefficient_hoare (right : Bool) (p : Plan) (i v j r a b : Nat)
    (ys : List Bool) (inp : Tape) (hi : Parked inp) :
    (coefficient right p).HoareTime (EmitPred inp (bank i v j r a b) ys)
      (EmitPred inp (bank i v j r a b) (ys ++ BinaryFields.encodeField
        (FormulaCoefficientPlan.value p r (if right then b else a)).bits))
      (3*max r (if right then b else a)+27) := by
  apply place_hoare _ 9 0 _ _ _ _ _ _ (parked i v j r a b)
    _ (FormulaCoefficientRound.operation_hoare right p r a b ys inp hi)
  intro t; fin_cases t <;> rfl

/-- The two physical predicates enter the actual live-index coefficient writer. -/
def railMachine (s right : Bool) (p : Plan) : TM 14 :=
  seqTM comparison (FormulaCoefficientGate.gate
    (seqTM (blocking s) (FormulaCoefficientGate.gate (coefficient right p))))

theorem rail_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (j r a b : Nat) (s right : Bool)
    (p : Plan) (ys : List Bool) :
    (railMachine s right p).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val j r a b) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j r a b)
        (ys ++ if i.val = j ∧ FormulaWiring.blocked φ i v s = true then
          BinaryFields.encodeField
            (FormulaCoefficientPlan.value p r (if right then b else a)).bits else []))
      (24*φ.encode.length+26*v.val+3*max i.val j+
        3*max r (if right then b else a)+240) := by
  have hi := word_parked φ.encode
  have hp := parked i.val v.val j r a b
  have hc := coefficient_hoare right p i.val v.val j r a b ys _ hi
  have hg := FormulaCoefficientGate.gate_hoare _ (FormulaWiring.blocked φ i v s)
    _ _ ys _ _ hi hp hc
  have hb := seqTM_hoareTime _ _ (blocking_hoare φ i v j r a b s ys)
    (emitPred_transition hi hp _) hg
  have ho := FormulaCoefficientGate.gate_hoare _ (decide (i.val=j)) _ _ ys _ _ hi hp hb
  have h := seqTM_hoareTime _ _ (comparison_hoare i.val v.val j r a b ys _ hi)
    (emitPred_transition hi hp _) ho
  have h' := h.mono_bound (show (3*max i.val j+20)+1+
      ((24*φ.encode.length+26*v.val+187)+1+
        (3*max r (if right then b else a)+27+2)+2) ≤
      24*φ.encode.length+26*v.val+3*max i.val j+
        3*max r (if right then b else a)+240 by omega)
  by_cases hij : i.val=j <;> cases hz : FormulaWiring.blocked φ i v s <;>
    simpa [railMachine,hij,hz] using h'

def portMachine (port : ControlSwitch.V) (s right : Bool) (p : Plan) : TM 14 :=
  if port = 3 then railMachine s right p else emitBitsTM []

theorem adjacency_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (j : Fin (FormulaWiring.levels φ+1))
    (port : ControlSwitch.V) (r a b : Nat) (s right : Bool) (p : Plan) (ys : List Bool) :
    (portMachine port s right p).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val j.val r a b) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j.val r a b)
        (ys ++ if FormulaWiring.adjacency φ (Sum.inr (.rail v s j)) (SwitchStack.sw i port)
          then BinaryFields.encodeField
            (FormulaCoefficientPlan.value p r (if right then b else a)).bits else []))
      (24*φ.encode.length+26*v.val+3*max i.val j.val+
        3*max r (if right then b else a)+240) := by
  by_cases ha : port = 3
  · subst port
    have he : FormulaWiring.adjacency φ (Sum.inr (.rail v s j)) (SwitchStack.sw i 3) ↔
        i.val = j.val ∧ FormulaWiring.blocked φ i v s = true := by
      change ((3 : ControlSwitch.V) = 2 ∨ 3 = 3) ∧ 3 = 3 ∧
        j.val = i.val ∧ FormulaWiring.blocked φ i v s = true ↔ _
      constructor
      · rintro ⟨_,_,hj,hb⟩; exact ⟨hj.symm,hb⟩
      · rintro ⟨hj,hb⟩; exact ⟨Or.inr rfl,rfl,hj.symm,hb⟩
    simpa only [portMachine,ite_eq_left rfl,he,ite_true] using
      rail_hoare φ i v j.val r a b s right p ys
  · have hn : ¬FormulaWiring.adjacency φ (Sum.inr (.rail v s j)) (SwitchStack.sw i port) :=
      fun he => ha he.2.1
    have h := (emitBitsTM_hoareTime ([] : List Bool) (word φ.encode)
      (bank i.val v.val j.val r a b) ys (word_parked _) (parked _ _ _ _ _ _)).mono_bound
      (show 0 ≤ 24*φ.encode.length+26*v.val+3*max i.val j.val+
        3*max r (if right then b else a)+240 by omega)
    unfold EmitPred
    simpa only [portMachine,ite_eq_right ha,ite_eq_right hn,List.append_nil] using h

/-- Exact interpretation of a canonical port in its tail/head role. -/
def tailMeaning (φ : SAT.CNF)
    (a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : FormulaWiring.Vertex φ :=
  FormulaIndexedGraph.vertexEquiv φ (MarkedGraph.decode _ (tailVertex a))

def headMeaning (φ : SAT.CNF)
    (b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : FormulaWiring.Vertex φ :=
  FormulaIndexedGraph.vertexEquiv φ (MarkedGraph.decode _ (headVertex b))

/-- Prepared canonical coordinates are the only interface premises: admission and
    coefficient value are derived, not supplied as oracle bits. -/
theorem canonical_rail_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (v : Fin (FormulaWiring.varCount φ)) (j : Fin (FormulaWiring.levels φ+1))
    (port : ControlSwitch.V) (s right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = Sum.inr (.rail v s j))
    (hb : headMeaning φ b = SwitchStack.sw i port) (ys : List Bool) :
    (portMachine port s right (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val j.val (index r) (index a) (index b)) ys)
      (EmitPred (word φ.encode) (bank i.val v.val j.val (index r) (index a) (index b))
        (ys ++ if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
            (FormulaIndexedGraph.terminals φ) (a,b) then
          BinaryFields.encodeField (FormulaOrderedTable.coefficient
            (FormulaIndexedGraph.terminals φ) right r (a,b)).bits else []))
      (24*φ.encode.length+26*v.val+3*max i.val j.val+
        3*(FormulaIndexedGraph.labels φ).length+240) := by
  have hd : tailVertex a ≠ headVertex b := by
    intro he
    have hh := congrArg (fun x => FormulaIndexedGraph.vertexEquiv φ
      (MarkedGraph.decode (FormulaIndexedGraph.terminals φ) x)) he
    change tailMeaning φ a = headMeaning φ b at hh
    rw [ha,hb] at hh
    cases hh
  have he : FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,b) ↔
      FormulaWiring.adjacency φ (Sum.inr (.rail v s j)) (SwitchStack.sw i port) := by
    change FormulaWiring.adjacency φ (tailMeaning φ a) (headMeaning φ b) ∧
      tailVertex a ≠ headVertex b ↔ _
    rw [ha,hb,and_iff_left hd]
  have h := adjacency_hoare φ i v j port (index r) (index a) (index b) s right
    (choose right (tag r) (tag a) (tag b)) ys
  have hr := FormulaCoefficientRound.index_bound r
  have hat := FormulaCoefficientRound.index_bound a
  have hbt := FormulaCoefficientRound.index_bound b
  have h' := h.mono_bound (show 24*φ.encode.length+26*v.val+3*max i.val j.val+
      3*max (index r) (if right then index b else index a)+240 ≤
      24*φ.encode.length+26*v.val+3*max i.val j.val+
        3*(FormulaIndexedGraph.labels φ).length+240 by
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

end UnconstrainedPACDetection.FormulaPairExecution

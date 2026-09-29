module

public import proofs.UnconstrainedPACDetection.FormulaPairExecution
public import proofs.UnconstrainedPACDetection.FormulaClauseRound

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClausePair
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaCoefficientPlan (Plan choose tag index)
open FormulaPairExecution (place_hoare tailMeaning headMeaning)

def bank (i c r a b : Nat) : Fin 10 → Tape :=
  ![regTape i,regTape 0,word [],regTape c,word [],
    regTape r,regTape a,regTape b,word [],word [true]]

theorem parked (i c r a b : Nat) : ∀ t, Parked (bank i c r a b t) := by
  intro t; fin_cases t
  all_goals first | exact parked_regTape _ | exact word_parked _

def query (exit : Bool) : TM 10 := placeWorkTM 0 5 (FormulaClauseRound.machine exit)
def coefficient (right : Bool) (p : Plan) : TM 10 :=
  placeWorkTM 5 0 (FormulaCoefficientRound.machine right p)
def body (exit right : Bool) (p : Plan) : TM 10 :=
  seqTM (query exit) (FormulaCoefficientGate.gate (coefficient right p))

theorem body_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (c r a b : Nat) (exit right : Bool) (p : Plan) (ys : List Bool) :
    (body exit right p).HoareTime (EmitPred (word φ.encode) (bank i.val c r a b) ys)
      (EmitPred (word φ.encode) (bank i.val c r a b)
        (ys ++ if FormulaClauseLookup.clauseMatch
          (FormulaClauseLookup.result φ.encode i.val) c exit then
          BinaryFields.encodeField
            (FormulaCoefficientPlan.value p r (if right then b else a)).bits else []))
      (20*φ.encode.length+6*c+3*max r (if right then b else a)+130) := by
  have hi := word_parked φ.encode
  have hp := parked i.val c r a b
  have hq := place_hoare _ 0 5 _ _ (bank i.val c r a b) _ _ _ hp
    (by intro t; fin_cases t <;> rfl) (FormulaClauseRound.decoded_hoare φ i c exit ys)
  have hc := place_hoare _ 5 0 _ _ (bank i.val c r a b) _ _ _ hp
    (by intro t; fin_cases t <;> rfl)
    (FormulaCoefficientRound.operation_hoare right p r a b ys _ hi)
  have hg := FormulaCoefficientGate.gate_hoare _
    (FormulaClauseLookup.clauseMatch (FormulaClauseLookup.result φ.encode i.val) c exit)
    _ _ ys _ _ hi hp hc
  have h := seqTM_hoareTime _ _ hq (emitPred_transition hi hp _) hg
  exact h.mono_bound (by omega)

def machine (port : ControlSwitch.V) (exit right : Bool) (p : Plan) : TM 10 :=
  if port = (if exit then 6 else 2) then body exit right p else emitBitsTM []

def fromVertex (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (c : Fin (φ.length+1)) (port : ControlSwitch.V) (exit : Bool) : FormulaWiring.Vertex φ :=
  if exit then SwitchStack.sw i port else Sum.inr (.clause c)

def toVertex (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (c : Fin (φ.length+1)) (port : ControlSwitch.V) (exit : Bool) : FormulaWiring.Vertex φ :=
  if exit then Sum.inr (.clause c) else SwitchStack.sw i port

theorem admission (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (c : Fin (φ.length+1)) (port : ControlSwitch.V) (exit : Bool) :
    FormulaWiring.adjacency φ (fromVertex φ i c port exit) (toVertex φ i c port exit) ↔
      port = (if exit then 6 else 2) ∧
        FormulaClauseLookup.clauseMatch (FormulaClauseLookup.result φ.encode i.val) c.val exit = true := by
  rw [FormulaClauseLookup.matches_lookup]
  cases exit <;> cases hl : FormulaWiring.lookup φ i with
  | none => simp [fromVertex,toVertex,FormulaWiring.adjacency,SwitchStack.Edge,
      SwitchStack.sw,FormulaWiring.DataWire,hl]
  | some z =>
    obtain ⟨k,l⟩ := z
    simp [fromVertex,toVertex,FormulaWiring.adjacency,SwitchStack.Edge,
      SwitchStack.sw,FormulaWiring.DataWire,hl]
    aesop

theorem adjacency_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (c : Fin (φ.length+1)) (port : ControlSwitch.V)
    (r a b : Nat) (exit right : Bool) (p : Plan) (ys : List Bool) :
    (machine port exit right p).HoareTime
      (EmitPred (word φ.encode) (bank i.val c.val r a b) ys)
      (EmitPred (word φ.encode) (bank i.val c.val r a b)
        (ys ++ if FormulaWiring.adjacency φ (fromVertex φ i c port exit)
            (toVertex φ i c port exit) then BinaryFields.encodeField
              (FormulaCoefficientPlan.value p r (if right then b else a)).bits else []))
      (20*φ.encode.length+6*c.val+3*max r (if right then b else a)+130) := by
  simp only [admission]
  by_cases hp : port = (if exit then 6 else 2)
  · simpa only [machine,ite_eq_left hp,hp,true_and,Bool.true_eq,ite_true] using
      body_hoare φ i c.val r a b exit right p ys
  · have h := (emitBitsTM_hoareTime ([] : List Bool) (word φ.encode)
      (bank i.val c.val r a b) ys (word_parked _) (parked _ _ _ _ _)).mono_bound
      (show 0 ≤ 20*φ.encode.length+6*c.val+3*max r (if right then b else a)+130 by omega)
    unfold EmitPred
    simpa only [machine,ite_eq_right hp,hp,false_and,ite_false,List.append_nil] using h

theorem canonical_hoare (φ : SAT.CNF) (i : Fin (FormulaWiring.levels φ))
    (c : Fin (φ.length+1)) (port : ControlSwitch.V) (exit right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = fromVertex φ i c port exit)
    (hb : headMeaning φ b = toVertex φ i c port exit) (ys : List Bool) :
    (machine port exit right (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred (word φ.encode) (bank i.val c.val (index r) (index a) (index b)) ys)
      (EmitPred (word φ.encode) (bank i.val c.val (index r) (index a) (index b))
        (ys ++ if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
          (FormulaIndexedGraph.terminals φ) (a,b) then BinaryFields.encodeField
            (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits else []))
      (20*φ.encode.length+6*c.val+3*(FormulaIndexedGraph.labels φ).length+130) := by
  have hd : tailVertex a ≠ headVertex b := by
    intro he
    have hh := congrArg (fun x => FormulaIndexedGraph.vertexEquiv φ
      (MarkedGraph.decode (FormulaIndexedGraph.terminals φ) x)) he
    change tailMeaning φ a = headMeaning φ b at hh
    rw [ha,hb] at hh
    cases exit <;> cases hh
  have he : FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,b) ↔ FormulaWiring.adjacency φ
      (fromVertex φ i c port exit) (toVertex φ i c port exit) := by
    change FormulaWiring.adjacency φ (tailMeaning φ a) (headMeaning φ b) ∧
      tailVertex a ≠ headVertex b ↔ _
    rw [ha,hb,and_iff_left hd]
  have h := adjacency_hoare φ i c port (index r) (index a) (index b) exit right
    (choose right (tag r) (tag a) (tag b)) ys
  have hr := FormulaCoefficientRound.index_bound r
  have hat := FormulaCoefficientRound.index_bound a
  have hbt := FormulaCoefficientRound.index_bound b
  have h' := h.mono_bound (show 20*φ.encode.length+6*c.val+
      3*max (index r) (if right then index b else index a)+130 ≤
      20*φ.encode.length+6*c.val+3*(FormulaIndexedGraph.labels φ).length+130 by
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

end UnconstrainedPACDetection.FormulaClausePair

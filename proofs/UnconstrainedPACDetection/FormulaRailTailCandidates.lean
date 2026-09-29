module

public import proofs.UnconstrainedPACDetection.FormulaRailTailPrepare
public import proofs.UnconstrainedPACDetection.FormulaRailSuccessor

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRailTailCandidates
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning headMeaning)
open FormulaRailHeadPrepare (bank parked)
open VerifierPairRestore (word word_parked)
open FormulaHeadFieldOrder (field)

def switchPort (φ : SAT.CNF) (i : Fin (levels φ)) :
    Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ) :=
  .inr ⟨(FormulaIndexedGraph.vertexEquiv φ).symm (SwitchStack.sw i 3),by
    rintro ⟨t,ht⟩
    have h := congrArg (FormulaIndexedGraph.vertexEquiv φ) ht
    cases t with
    | inl t => cases t <;> simp [FormulaIndexedGraph.terminals,PACFormulaReduction.terminals,
        PACFormulaReduction.terminal,FormulaWiring.sourceP,FormulaWiring.sourceQ,SwitchStack.sw] at h
    | inr t => cases t <;> simp [FormulaIndexedGraph.terminals,PACFormulaReduction.terminals,
        PACFormulaReduction.terminal,FormulaWiring.sinkP,FormulaWiring.sinkQ,SwitchStack.sw] at h⟩

theorem switch_meaning (φ : SAT.CNF) (i : Fin (levels φ)) :
    headMeaning φ (switchPort φ i) = SwitchStack.sw i 3 := by
  simp [headMeaning,switchPort,headVertex,MarkedGraph.decode]

theorem switch_index (φ : SAT.CNF) (i : Fin (levels φ)) : index (switchPort φ i) = 20*i.val+3 :=
  FormulaSwitchCursor.index φ i 3

def switchQuery (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 17 :=
  placeWorkTM 0 3 (FormulaPairExecution.portMachine 3 s right plan)

theorem switch_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (v : Fin (varCount φ)) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.rail v s i.castSucc)) (f : Nat) (ys : List Bool) :
    (switchQuery s right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val i.val (index r) (index a) (20*i.val+3) f (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (bank i.val v.val i.val (index r) (index a) (20*i.val+3) f (levels φ) (varCount φ))
        (ys ++ field φ right r a (switchPort φ i)))
      (24*φ.encode.length+26*v.val+3*i.val+3*(FormulaIndexedGraph.labels φ).length+240) := by
  have h := FormulaPairExecution.canonical_rail_hoare φ i v i.castSucc 3 s right r a
    (switchPort φ i) ha (switch_meaning φ i) ys
  have ht : tag (switchPort φ i) = none := rfl
  rw [switch_index,ht] at h
  simp only [Fin.val_castSucc,Nat.max_self] at h
  exact FormulaPairExecution.place_hoare _ 0 3 _ _ _ _ _ _
    (parked _ _ _ _ _ _ _ _ _) (by intro t; fin_cases t <;> rfl) h

theorem tail_index (φ : SAT.CNF) (v : Fin (varCount φ)) (s : Bool) (j : Fin (levels φ+1))
    (a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.rail v s j)) : index a = index (FormulaRailCursor.port φ v s j) := by
  cases a with
  | inl t =>
    cases t <;> simp [tailMeaning,tailVertex,MarkedGraph.decode,FormulaIndexedGraph.terminals,
      PACFormulaReduction.terminals,PACFormulaReduction.terminal,FormulaWiring.sourceP,FormulaWiring.sourceQ,
      SwitchStack.sw] at ha
  | inr x =>
    have hx : x.val = (FormulaIndexedGraph.vertexEquiv φ).symm (.inr (.rail v s j)) := by
      apply (FormulaIndexedGraph.vertexEquiv φ).injective
      simpa [tailMeaning,tailVertex,MarkedGraph.decode] using ha
    exact congrArg Fin.val hx

theorem successor_index (φ : SAT.CNF) (i : Fin (levels φ)) (v : Fin (varCount φ)) (s : Bool)
    (a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.rail v s i.castSucc)) :
    index (FormulaRailCursor.port φ v s i.succ) = index a+1 := by
  obtain ⟨pre,post,hp,_⟩ := FormulaRailBase.factor φ v s
  rw [tail_index φ v s i.castSucc a ha,
    FormulaRailCursor.port_index φ v s pre post hp i.castSucc,
    FormulaRailCursor.port_index φ v s pre post hp i.succ]
  simp only [Fin.val_succ,Fin.val_castSucc]
  omega

def successorQuery (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 17 :=
  placeWorkTM 0 2 (FormulaRailSuccessor.machine false s s right plan)

theorem successor_hoare (φ : SAT.CNF) (i : Fin (levels φ)) (v : Fin (varCount φ)) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.rail v s i.castSucc)) (ys : List Bool) :
    (successorQuery s right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i.val v.val (i.val+1) (index r) (index a) (index a+1) v.val (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (bank i.val v.val (i.val+1) (index r) (index a) (index a+1) v.val (levels φ) (varCount φ))
        (ys ++ field φ right r a (FormulaRailCursor.port φ v s i.succ)))
      (24*φ.encode.length+29*v.val+7*i.val+3*(FormulaIndexedGraph.labels φ).length+278) := by
  have h := FormulaRailSuccessor.canonical_hoare φ i v v i.succ s s right r a
    (FormulaRailCursor.port φ v s i.succ) ha (FormulaRailCursor.port_meaning φ v s i.succ) ys
  have ht : tag (FormulaRailCursor.port φ v s i.succ) = none := rfl
  rw [successor_index φ i v s a ha,ht] at h
  simp only [Fin.val_succ,Nat.max_self] at h
  have h' := FormulaPairExecution.place_hoare _ 0 2 _ _ _ _ _ _
    (parked i.val v.val (i.val+1) (index r) (index a) (index a+1) v.val (levels φ) (varCount φ))
    (by intro t; fin_cases t <;> rfl) h
  exact h'.mono_bound (by omega)

end UnconstrainedPACDetection.FormulaRailTailCandidates

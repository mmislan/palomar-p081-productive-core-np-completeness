module

public import proofs.UnconstrainedPACDetection.FormulaClauseTailCanonical

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVariableTailHeads
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open FormulaRailHeadPrepare (bank parked)
open FormulaHeadFieldOrder (field)

def route : Equiv.Perm (Fin 17) where
  toFun := ![9,10,11,12,13,0,1,2,3,4,5,6,7,8,14,15,16]
  invFun := ![5,6,7,8,9,10,11,12,13,0,1,2,3,4,14,15,16]
  left_inv := by intro t; fin_cases t <;> rfl
  right_inv := by intro t; fin_cases t <;> rfl

def emit (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 17 :=
  VerifierWorkPermutation.machine (placeWorkTM 0 12 (FormulaCoefficientRound.machine right plan)) route

theorem emit_hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var v.castSucc)) (i j f : Nat) (ys : List Bool) :
    (emit right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i v.val j (index r) (index a)
        (FormulaRailBase.value (levels φ) (varCount φ) v.val s) f (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (bank i v.val j (index r) (index a)
        (FormulaRailBase.value (levels φ) (varCount φ) v.val s) f (levels φ) (varCount φ))
        (ys ++ field φ right r a (FormulaRailCursor.port φ v s 0)))
      (3*(FormulaIndexedGraph.labels φ).length+27) := by
  let b := FormulaRailCursor.port φ v s 0
  have hb : index b = FormulaRailBase.value (levels φ) (varCount φ) v.val s := by
    obtain ⟨pre,post,hp,hl⟩ := FormulaRailBase.factor φ v s
    simpa [b,hl] using FormulaRailCursor.port_index φ v s pre post hp 0
  have ht : tag b = none := rfl
  have he : FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,b) := by
    rw [FormulaHeadFieldOrder.arc_meaning,ha,FormulaRailCursor.port_meaning]
    change v.val=v.val ∧ (0 : Fin (levels φ+1)).val=0
    exact ⟨rfl,rfl⟩
  have h := FormulaCoefficientRound.arc_hoare (FormulaIndexedGraph.edge φ)
    (FormulaIndexedGraph.terminals φ) right r ⟨(a,b),he⟩ ys (word φ.encode) (word_parked _)
  have hf : field φ right r a b = BinaryFields.encodeField
      (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits := ite_eq_left he
  rw [← hf,hb,ht] at h
  exact FormulaRoutedFrame.hoare _ 0 12 route _ _ _ _ _ _
    (parked _ _ _ _ _ _ _ _ _) (by intro t; fin_cases t <;> rfl) h

def round (s right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 17 :=
  seqTM (FormulaRailBaseRegisters.machine s) (emit right plan)

theorem round_hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (s right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var v.castSucc)) (i j b f M : Nat) (ys : List Bool)
    (hL : levels φ ≤ M) (hV : varCount φ ≤ M) (hv : v.val ≤ M) (hb : b ≤ M)
    (hs : FormulaRailBase.value (levels φ) (varCount φ) v.val s ≤ M) :
    (round s right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i v.val j (index r) (index a) b f (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (bank i v.val j (index r) (index a)
        (FormulaRailBase.value (levels φ) (varCount φ) v.val s) f (levels φ) (varCount φ))
        (ys ++ field φ right r a (FormulaRailCursor.port φ v s 0)))
      (40*(opBudget M+1)+3*(FormulaIndexedGraph.labels φ).length+28) := by
  have h0 := FormulaRailBaseRegisters.arithmetic_hoare (levels φ) (varCount φ) v.val b M s
    (word φ.encode) (bank i v.val j (index r) (index a) b f (levels φ) (varCount φ)) ys
    (word_parked _) (parked _ _ _ _ _ _ _ _ _) rfl rfl rfl rfl hL hV hv hb hs
  have he : FormulaRailBaseRegisters.bank
      (bank i v.val j (index r) (index a) b f (levels φ) (varCount φ))
      (FormulaRailBase.value (levels φ) (varCount φ) v.val s) =
      bank i v.val j (index r) (index a)
        (FormulaRailBase.value (levels φ) (varCount φ) v.val s) f (levels φ) (varCount φ) := by
    funext t; fin_cases t <;> simp [FormulaRailBaseRegisters.bank,bank]
  rw [he] at h0
  have h1 := emit_hoare φ v s right r a ha i j f ys
  exact (seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _) _) h1).mono_bound (by omega)

def machine (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 17 :=
  seqTM (round false right plan) (round true right plan)

theorem hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var v.castSucc)) (i j b f M : Nat) (ys : List Bool)
    (hL : levels φ ≤ M) (hV : varCount φ ≤ M) (hv : v.val ≤ M) (hb : b ≤ M)
    (hs : ∀ s, FormulaRailBase.value (levels φ) (varCount φ) v.val s ≤ M) :
    (machine right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i v.val j (index r) (index a) b f (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (bank i v.val j (index r) (index a)
        (FormulaRailBase.value (levels φ) (varCount φ) v.val true) f (levels φ) (varCount φ))
        (ys ++ field φ right r a (FormulaRailCursor.port φ v false 0) ++
          field φ right r a (FormulaRailCursor.port φ v true 0)))
      (80*(opBudget M+1)+6*(FormulaIndexedGraph.labels φ).length+57) := by
  have h0 := round_hoare φ v false right r a ha i j b f M ys hL hV hv hb (hs false)
  have h1 := round_hoare φ v true right r a ha i j
    (FormulaRailBase.value (levels φ) (varCount φ) v.val false) f M
    (ys ++ field φ right r a (FormulaRailCursor.port φ v false 0)) hL hV hv (hs false) (hs true)
  exact (seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _) _) h1).mono_bound (by omega)

end UnconstrainedPACDetection.FormulaVariableTailHeads

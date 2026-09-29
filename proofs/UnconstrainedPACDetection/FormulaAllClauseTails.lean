module

public import proofs.UnconstrainedPACDetection.FormulaClauseTailReturn

@[expose] public section

namespace UnconstrainedPACDetection.FormulaAllClauseTails
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)

def bits (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : List Bool :=
  (List.finRange φ.length).flatMap (fun c =>
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaHeadFieldOrder.field φ right r (FormulaClauseCursor.port φ c)))

theorem bits_eq (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    FormulaClauseTailLoop.bits φ right r φ.length = bits φ right r := by
  have h := FormulaHeadFieldOrder.range_fields φ.length (fun c =>
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaHeadFieldOrder.field φ right r (FormulaClauseCursor.port φ c)))
  exact h

def machine (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 22 :=
  seqTM FormulaClauseTailInit.machine (seqTM (FormulaClauseTailLoop.machine right plan) FormulaClauseTailReturn.machine)

def budget (φ : SAT.CNF) : Nat := 57*opBudget (cap φ)+
  φ.length*(FormulaClauseTailBody.budget φ+2)+(φ.length+2)+58

theorem canonical_hoare (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (f g : Nat) (ys : List Bool)
    (hf : f ≤ cap φ) (hg : g ≤ cap φ) :
    (machine right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (FormulaClauseTailInit.frame (index r) (levels φ) (varCount φ) φ.length f g) ys)
      (EmitPred (word φ.encode) (FormulaClauseTailInit.frame (index r) (levels φ) (varCount φ) φ.length
        (varCount φ) φ.length) (ys ++ bits φ right r)) (budget φ) := by
  have h0 := FormulaClauseTailInit.hoare φ (index r) f g ys hf hg
  have h1 := FormulaClauseTailLoop.canonical_hoare φ right r ys
  have h2 := FormulaClauseTailReturn.hoare φ (index r) (ys ++ FormulaClauseTailLoop.bits φ right r φ.length)
  have h12 := seqTM_hoareTime _ _ h1
    (emitPred_transition (word_parked _) (FormulaClauseTailLoop.parked _ _ _ _ _ _ _ (parked_regTape _)) _) h2
  have h := seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (FormulaClauseTailLoop.parked _ _ _ _ _ _ _ (parked_regTape _)) _) h12
  rw [bits_eq] at h
  exact h.mono_bound (by unfold budget; omega)

end UnconstrainedPACDetection.FormulaAllClauseTails

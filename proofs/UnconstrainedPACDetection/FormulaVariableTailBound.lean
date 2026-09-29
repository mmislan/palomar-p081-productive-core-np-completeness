module

public import proofs.UnconstrainedPACDetection.FormulaVariableTailCanonical

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVariableTailBound
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open FormulaRailHeadPrepare (bank)
open VerifierPairRestore (word)

def cap (φ : SAT.CNF) : Nat := 100*(φ.encode.length+2)^2

theorem base_bound (φ : SAT.CNF) (v : Fin (varCount φ)) (s : Bool) :
    FormulaRailBase.value (levels φ) (varCount φ) v.val s ≤ cap φ := by
  obtain ⟨pre,post,hp,hl⟩ := FormulaRailBase.factor φ v s
  have hb := FormulaRailCursor.port_index φ v s pre post hp 0
  simp only [hl,Fin.val_zero,Nat.add_zero] at hb
  have hi := FormulaCoefficientRound.index_bound (FormulaRailCursor.port φ v s 0)
  rw [hb] at hi
  have hn := FormulaIndexedGraph.labels_bound φ
  apply hi.trans (hn.trans _)
  unfold cap
  nlinarith only [Nat.zero_le φ.encode.length]

theorem canonical_hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var v.castSucc)) (i j b f : Nat) (ys : List Bool)
    (hb : b ≤ cap φ) :
    (FormulaVariableTailHeads.machine right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank i v.val j (index r) (index a) b f (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (bank i v.val j (index r) (index a)
        (FormulaRailBase.value (levels φ) (varCount φ) v.val true) f (levels φ) (varCount φ))
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
          (FormulaHeadFieldOrder.field φ right r a)))
      (80*(opBudget (cap φ)+1)+6*(FormulaIndexedGraph.labels φ).length+57) := by
  obtain ⟨hL,hV,_⟩ := FormulaEnumeration.parameter_bounds φ
  have hv := v.isLt
  apply FormulaVariableTailCanonical.canonical_hoare φ v right r a ha i j b f (cap φ) ys
  · unfold cap; nlinarith
  · unfold cap; nlinarith
  · unfold cap; nlinarith
  · exact hb
  · exact base_bound φ v

end UnconstrainedPACDetection.FormulaVariableTailBound

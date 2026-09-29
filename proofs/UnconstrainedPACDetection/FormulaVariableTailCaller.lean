module

public import proofs.UnconstrainedPACDetection.FormulaVariableTailBound

@[expose] public section

namespace UnconstrainedPACDetection.FormulaVariableTailCaller
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning)
open FormulaRailHeadPrepare (bank parked)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)

theorem copy_variable (i v j r a b f L V : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    (copyIntoTM (0 : Fin 17) 5).HoareTime
      (EmitPred inp (bank i v j r a b f L V) ys)
      (EmitPred inp (bank i i j r a b f L V) ys) (2*v+2*i^2+7*i+7) := by
  have h := copyIntoTM_hoareTime (0 : Fin 17) 5 (by decide) i v inp (bank i v j r a b f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl
  have he : Function.update (bank i v j r a b f L V) 5 (regTape i) = bank i i j r a b f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he] at h
  exact h.mono_bound (by nlinarith)

theorem restore_variable (i v j r a b f L V : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    (copyIntoTM (16 : Fin 17) 5).HoareTime
      (EmitPred inp (bank i v j r a b f L V) ys)
      (EmitPred inp (bank i V j r a b f L V) ys) (2*v+2*V^2+7*V+7) := by
  have h := copyIntoTM_hoareTime (16 : Fin 17) 5 (by decide) V v inp (bank i v j r a b f L V) ys hi
    (fun t _ => parked _ _ _ _ _ _ _ _ _ t) rfl rfl
  have he : Function.update (bank i v j r a b f L V) 5 (regTape V) = bank i V j r a b f L V := by
    funext t; fin_cases t <;> simp [bank]
  rw [he] at h
  exact h.mono_bound (by nlinarith)

def machine (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 17 :=
  seqTM (copyIntoTM 0 5) (seqTM (FormulaVariableTailHeads.machine right plan) (copyIntoTM 16 5))

theorem canonical_hoare (φ : SAT.CNF) (v : Fin (varCount φ)) (right : Bool)
    (r a : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = .inr (.var v.castSucc)) (j b f : Nat) (ys : List Bool)
    (hb : b ≤ cap φ) :
    (machine right (choose right (tag r) (tag a) none)).HoareTime
      (EmitPred (word φ.encode) (bank v.val (varCount φ) j (index r) (index a) b f (levels φ) (varCount φ)) ys)
      (EmitPred (word φ.encode) (bank v.val (varCount φ) j (index r) (index a)
        (FormulaRailBase.value (levels φ) (varCount φ) v.val true) f (levels φ) (varCount φ))
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
          (FormulaHeadFieldOrder.field φ right r a)))
      (80*(opBudget (cap φ)+1)+6*(FormulaIndexedGraph.labels φ).length+
        4*(varCount φ)^2+18*varCount φ+73) := by
  have h0 := copy_variable v.val (varCount φ) j (index r) (index a) b f (levels φ) (varCount φ)
    (word φ.encode) (word_parked _) ys
  have h1 := FormulaVariableTailBound.canonical_hoare φ v right r a ha v.val j b f ys hb
  have h2 := restore_variable v.val v.val j (index r) (index a)
    (FormulaRailBase.value (levels φ) (varCount φ) v.val true) f (levels φ) (varCount φ)
    (word φ.encode) (word_parked _)
    (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaHeadFieldOrder.field φ right r a))
  have h12 := seqTM_hoareTime _ _ h1
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _) _) h2
  have h := seqTM_hoareTime _ _ h0
    (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _ _ _) _) h12
  have hv := v.isLt
  exact h.mono_bound (by nlinarith)

end UnconstrainedPACDetection.FormulaVariableTailCaller

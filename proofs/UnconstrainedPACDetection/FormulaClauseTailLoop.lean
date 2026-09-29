module

public import proofs.UnconstrainedPACDetection.FormulaClauseTailBody

@[expose] public section

namespace UnconstrainedPACDetection.FormulaClauseTailLoop
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open VerifierPairRestore (word word_parked)
open FormulaChangingFrame (extend)

def frame (c r A L V C : Nat) (fuel : Tape) : Fin 22 → Tape :=
  extend (FormulaClauseTailHeads.frame 0 c r (A+c) 0 L V C (regTape L)) fuel

theorem parked (c r A L V C : Nat) (fuel : Tape) (hf : Parked fuel) :
    ∀ t, Parked (frame c r A L V C fuel t) :=
  FormulaChangingFrame.parked _ _ (FormulaClauseTailHeads.parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) hf

def body (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 22 :=
  placeWorkTM 0 1 (FormulaClauseTailBody.machine right plan)

theorem body_hoare (φ : SAT.CNF) (c : Fin φ.length) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) :
    (body right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (frame c.val (index r) (FormulaClauseCursor.base φ)
        (levels φ) (varCount φ) φ.length fuel) ys)
      (EmitPred (word φ.encode) (frame (c.val+1) (index r) (FormulaClauseCursor.base φ)
        (levels φ) (varCount φ) φ.length fuel)
        (ys ++ (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
          (FormulaHeadFieldOrder.field φ right r (FormulaClauseCursor.port φ c))))
      (FormulaClauseTailBody.budget φ) := by
  exact FormulaChangingFrame.append_hoare _ _ _ _ fuel _ _ _
    (FormulaClauseTailHeads.parked _ _ _ _ _ _ _ _ _ (parked_regTape _)) hf
    (FormulaClauseTailBody.hoare φ c right r ys)

def fields (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  if hk : k < φ.length then
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaHeadFieldOrder.field φ right r (FormulaClauseCursor.port φ ⟨k,hk⟩))
  else []

def bits (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (k : Nat) : List Bool :=
  (List.range k).flatMap (fields φ right r)

def machine (right : Bool) (plan : FormulaCoefficientPlan.Plan) : TM 22 := forRegTM (body right plan) 21

theorem canonical_hoare (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (ys : List Bool) :
    (machine right (choose right (tag r) none none)).HoareTime
      (EmitPred (word φ.encode) (frame 0 (index r) (FormulaClauseCursor.base φ)
        (levels φ) (varCount φ) φ.length (regTape φ.length)) ys)
      (EmitPred (word φ.encode) (frame φ.length (index r) (FormulaClauseCursor.base φ)
        (levels φ) (varCount φ) φ.length (regTape φ.length))
        (ys ++ bits φ right r φ.length))
      (φ.length*(FormulaClauseTailBody.budget φ+2)+(φ.length+2)) := by
  let C := φ.length
  let A := FormulaClauseCursor.base φ
  let w := fun k => frame k (index r) A (levels φ) (varCount φ) C (regTape C)
  let zs := fun k => ys ++ bits φ right r k
  have h := forRegTM_hoareTime (body right (choose right (tag r) none none)) (21 : Fin 22) C
    (word φ.encode) w zs (FormulaClauseTailBody.budget φ) (word_parked _)
    (by intro k; rfl) (by intro k t _; exact parked _ _ _ _ _ _ _ (parked_regTape _) t) (by
      intro k hk
      let fuel : Tape := ⟨k+2,regCells C⟩
      have hf : Parked fuel := parked_regCells (by omega)
      have he (z : Nat) : Function.update (w z) 21 fuel = frame z (index r) A (levels φ) (varCount φ) C fuel := by
        funext t; fin_cases t <;> simp [w,frame,extend]
      have hb := body_hoare φ ⟨k,hk⟩ right r fuel hf (zs k)
      have heq : fields φ right r k =
          (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
            (FormulaHeadFieldOrder.field φ right r (FormulaClauseCursor.port φ ⟨k,hk⟩)) := by
        unfold fields; rw [dite_eq_left hk]
      have hy : zs (k+1) = zs k ++ fields φ right r k := by
        simp [zs,bits,List.range_succ,List.flatMap_append,List.append_assoc]
      rw [he,he,hy,heq]
      exact hb)
  simpa only [machine,w,zs,bits,List.range_zero,List.flatMap_nil,List.append_nil,C,A,Nat.add_assoc] using h

end UnconstrainedPACDetection.FormulaClauseTailLoop

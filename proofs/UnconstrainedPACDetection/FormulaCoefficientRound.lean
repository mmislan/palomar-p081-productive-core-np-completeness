module

public import proofs.UnconstrainedPACDetection.FormulaCoefficientPlan
public import proofs.UnconstrainedPACDetection.VerifierWorkPermutation

@[expose] public section

namespace UnconstrainedPACDetection.FormulaCoefficientRound
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaCoefficientPlan (Plan choose tag index)

def bank (r a b : Nat) : Fin 5 → Tape :=
  ![regTape r,regTape a,regTape b,word [],word [true]]

theorem parked (r a b : Nat) : ∀ j, Parked (bank r a b j) := by
  intro j; fin_cases j
  all_goals first | exact parked_regTape _ | exact word_parked _

def leftPermutation : Equiv.Perm (Fin 5) := (Equiv.swap 2 3).trans (Equiv.swap 2 4)
def permutation (right : Bool) : Equiv.Perm (Fin 5) :=
  if right then leftPermutation.trans (Equiv.swap 1 2) else leftPermutation

def placed (p : Plan) : TM 5 := placeWorkTM 0 1 (FormulaCoefficientPlan.machine p)
def machine (right : Bool) (p : Plan) : TM 5 :=
  VerifierWorkPermutation.machine (placed p) (permutation right)

/-- Read the selected live endpoint while retaining both endpoint counters. -/
theorem operation_hoare (right : Bool) (p : Plan) (r a b : Nat) (ys : List Bool)
    (inp : Tape) (hi : Parked inp) : (machine right p).HoareTime
    (EmitPred inp (bank r a b) ys)
    (EmitPred inp (bank r a b)
      (ys ++ BinaryFields.encodeField (FormulaCoefficientPlan.value p r (if right then b else a)).bits))
    (3*max r (if right then b else a)+27) := by
  rintro inp' w out ⟨hin,hw,ho⟩
  subst inp'
  subst w
  let base : Fin 5 → Tape := fun j => bank r a b (permutation right j)
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := FormulaCoefficientPlan.operation_hoare p r
    (if right then b else a) ys inp hi inp
    (FormulaClauseCompare.bank r (if right then b else a) [true]) out ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal (FormulaCoefficientPlan.machine p)
    0 1 base hr (by intro j _; exact (parked r a b (permutation right j)).read_ne_start)
  have routed := VerifierWorkPermutation.run_commute (placed p) (permutation right) hs
  refine ⟨VerifierWorkPermutation.wrap (placed p) (permutation right)
    (placeWorkCfg _ 0 1 base d),t,ht,?_,hh,hdi,?_,hdo⟩
  · unfold machine
    convert routed using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; cases right <;> fin_cases j <;>
        simp [VerifierWorkPermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
          base,permutation,leftPermutation,Equiv.trans_apply,Equiv.swap_apply_def,
          bank,FormulaClauseCompare.bank]
    · rfl
  · funext j; cases right <;> fin_cases j <;>
      simp [VerifierWorkPermutation.wrap,placeWorkCfg,placeWorkInMiddle,placeWorkCoord,
        base,permutation,leftPermutation,Equiv.trans_apply,Equiv.swap_apply_def,
        bank,FormulaClauseCompare.bank,hdw]

theorem index_bound {n : Nat} {T : (Bool ⊕ Bool) ↪ Fin n}
    (r : Bool ⊕ MarkedGraph.Internal T) : index r ≤ n := by
  cases r with
  | inl b => exact Nat.zero_le _
  | inr x => exact Nat.le_of_lt x.val.isLt

/-- Every accepted canonical arc gets its actual coefficient field, including zero. -/
theorem arc_hoare {n : Nat} (A : Fin n → Fin n → Prop) [DecidableRel A]
    (T : (Bool ⊕ Bool) ↪ Fin n) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal T) (e : FromAdjacency.Arcs (MarkedGraph.pulled A T))
    (ys : List Bool) (inp : Tape) (hi : Parked inp) :
    (machine right (choose right (tag r) (tag e.val.1) (tag e.val.2))).HoareTime
      (EmitPred inp (bank (index r) (index e.val.1) (index e.val.2)) ys)
      (EmitPred inp (bank (index r) (index e.val.1) (index e.val.2))
        (ys ++ BinaryFields.encodeField
          (FormulaOrderedTable.coefficient T right r e.val).bits)) (3*n+27) := by
  have hn : tailRow e.val.1 ≠ headRow e.val.2 :=
    rows_distinct (FromAdjacency.network (MarkedGraph.pulled A T)) e
  have hc := FormulaCoefficientPlan.coefficient_value T right r e.val.1 e.val.2 hn
  have h := operation_hoare right (choose right (tag r) (tag e.val.1) (tag e.val.2))
    (index r) (index e.val.1) (index e.val.2) ys inp hi
  have he : index (if right then e.val.2 else e.val.1) =
      if right then index e.val.2 else index e.val.1 := by cases right <;> rfl
  rw [he] at hc
  rw [hc] at h
  have hr := index_bound r
  have ha := index_bound e.val.1
  have hb := index_bound e.val.2
  exact h.mono_bound (by cases right <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega)

end UnconstrainedPACDetection.FormulaCoefficientRound

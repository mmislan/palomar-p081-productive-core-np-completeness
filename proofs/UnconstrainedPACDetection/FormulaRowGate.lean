module

public import proofs.UnconstrainedPACDetection.FormulaRowQuery

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRowGate
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (tag index)

def frame (φ : SAT.CNF) (k : Nat) (fuel : Tape) : Fin 28 → Tape :=
  FormulaRowQuery.frame k (levels φ) (varCount φ) φ.length (20*(levels φ-1))
    (FormulaClauseCursor.base φ+φ.length) (FormulaIndexedGraph.labels φ).length fuel

def field (φ : SAT.CNF) (right : Bool) (k : Fin (FormulaIndexedGraph.labels φ).length) : List Bool :=
  if hk : k ∉ Set.range (FormulaIndexedGraph.terminals φ) then
    (FormulaOrderedTable.rows (FormulaIndexedGraph.terminals φ)).flatMap
      (FormulaVertexTailFields.port φ right (.inr ⟨k,hk⟩)) else []

def machine (right : Bool) : TM 28 := FormulaNegativeChain.machine
  [FormulaRowQuery.query 0,FormulaRowQuery.query 1,FormulaRowQuery.query 2,FormulaRowQuery.query 3]
  (placeWorkTM 0 6 (FormulaAllTails.machine right none))

def budget (φ : SAT.CNF) : Nat := FormulaAllTails.budget φ+28*(FormulaIndexedGraph.labels φ).length+152

theorem value_lt (φ : SAT.CNF) (q : Fin 4) :
    FormulaRowQuery.value (20*(levels φ-1)) (FormulaClauseCursor.base φ+φ.length) q < (FormulaIndexedGraph.labels φ).length := by
  have h (t : Bool ⊕ Bool) := (FormulaIndexedGraph.terminals φ t).isLt
  simp only [FormulaRowBoundary.terminal_index] at h
  fin_cases q
  · exact h (.inl false)
  · exact h (.inr true)
  · exact h (.inl true)
  · exact h (.inr false)

theorem hoare (φ : SAT.CNF) (k : Fin (FormulaIndexedGraph.labels φ).length) (right : Bool)
    (fuel : Tape) (hf : Parked fuel) (ys : List Bool) : (machine right).HoareTime
      (EmitPred (word φ.encode) (frame φ k.val fuel) ys)
      (EmitPred (word φ.encode) (frame φ k.val fuel) (ys ++ field φ right k)) (budget φ) := by
  let v := FormulaRowQuery.value (20*(levels φ-1)) (FormulaClauseCursor.base φ+φ.length)
  let spec := fun q : Fin 4 => (FormulaRowQuery.query q,decide (k.val=v q),4*k.val+3*max (k.val+1) (v q)+32)
  let checks := [spec 0,spec 1,spec 2,spec 3]
  have hp := FormulaRowQuery.parked k.val (levels φ) (varCount φ) φ.length
    (20*(levels φ-1)) (FormulaClauseCursor.base φ+φ.length) (FormulaIndexedGraph.labels φ).length fuel hf
  have hc : (∀ q ∈ checks, q.2.1=false) ↔ k ∉ Set.range (FormulaIndexedGraph.terminals φ) := by
    rw [FormulaRowBoundary.internal_iff]
    simp [checks,spec,v,FormulaRowQuery.value]
    constructor
    · rintro ⟨h1,h4,hq,hp⟩
      exact ⟨of_decide_eq_false h1,of_decide_eq_false h4,
        of_decide_eq_false hq,of_decide_eq_false hp⟩
    · rintro ⟨h1,h4,hq,hp⟩
      exact ⟨decide_eq_false h1,decide_eq_false h4,decide_eq_false hq,decide_eq_false hp⟩
  have hq : ∀ q ∈ checks, ∀ xs, q.1.HoareTime (EmitPred (word φ.encode) (frame φ k.val fuel) xs)
      (EmitPred (word φ.encode) (frame φ k.val fuel) (xs ++ [q.2.1])) q.2.2 := by
    intro q hq xs
    have hh (j : Fin 4) := FormulaRowQuery.hoare j k.val (levels φ) (varCount φ) φ.length
      (20*(levels φ-1)) (FormulaClauseCursor.base φ+φ.length) (FormulaIndexedGraph.labels φ).length
      fuel hf (word φ.encode) (word_parked _) xs
    simp only [checks,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hh 0
    · exact hh 1
    · exact hh 2
    · exact hh 3
  have hb : (∀ q ∈ checks, q.2.1=false) → ∀ xs,
      (placeWorkTM 0 6 (FormulaAllTails.machine right none)).HoareTime
        (EmitPred (word φ.encode) (frame φ k.val fuel) xs)
        (EmitPred (word φ.encode) (frame φ k.val fuel) (xs ++ field φ right k)) (FormulaAllTails.budget φ) := by
    intro h xs
    have hk := hc.mp h
    have ht := FormulaAllTails.canonical_hoare φ right (.inr ⟨k,hk⟩) xs
    have hl := FormulaPairExecution.place_hoare _ 0 6 _ _ (frame φ k.val fuel) _ _ _ hp
      (by intro t; fin_cases t <;> rfl) ht
    simpa only [field,dite_eq_left hk,tag] using hl
  have h := FormulaNegativeChain.hoare checks (placeWorkTM 0 6 (FormulaAllTails.machine right none))
    (word φ.encode) (frame φ k.val fuel) (field φ right k) (FormulaAllTails.budget φ) (word_parked _) hp hq hb ys
  have he : (if ∀ q ∈ checks, q.2.1=false then field φ right k else []) = field φ right k := by
    by_cases hk : k ∉ Set.range (FormulaIndexedGraph.terminals φ)
    · rw [ite_eq_left (hc.mpr hk)]
    · rw [ite_eq_right (fun h => hk (hc.mp h))]; unfold field; rw [dite_eq_right hk]
  rw [he] at h
  have hbound (q : Fin 4) : 4*k.val+3*max (k.val+1) (v q)+32 ≤ 7*(FormulaIndexedGraph.labels φ).length+35 := by
    have hk := k.isLt
    have hv := value_lt φ q
    change v q < _ at hv
    omega
  have hbnd : FormulaNegativeChain.cost checks (FormulaAllTails.budget φ) ≤ budget φ := by
    have h0 := hbound 0; have h1 := hbound 1; have h2 := hbound 2; have h3 := hbound 3
    simp only [FormulaNegativeChain.cost,checks,spec,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    unfold budget
    omega
  exact h.mono_bound hbnd

end UnconstrainedPACDetection.FormulaRowGate

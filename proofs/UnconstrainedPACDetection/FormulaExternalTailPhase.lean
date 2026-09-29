module

public import proofs.UnconstrainedPACDetection.FormulaVertexTailFields

@[expose] public section

namespace UnconstrainedPACDetection.FormulaExternalTailPhase
open Complexity Complexity.TM DirectedLinkageSource
open FormulaWiring (levels varCount)
open FormulaCoefficientPlan (choose tag index)
open VerifierPairRestore (word word_parked)
open FormulaVariableTailBound (cap)

def vertices (φ : SAT.CNF) : List (FormulaWiring.Vertex φ) :=
  FormulaOtherHeadOrder.variableHeads φ ++ FormulaOtherHeadOrder.rails φ ++ FormulaOtherHeadOrder.clauses φ

def bits (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) : List Bool :=
  (vertices φ).flatMap (FormulaVertexTailFields.vertex φ right r)

theorem bits_eq (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) :
    FormulaAllVariableTails.bits φ right r ++ FormulaAllRailTails.bits φ right r (varCount φ) ++
      FormulaAllClauseTails.bits φ right r = bits φ right r := by
  simp only [bits,vertices,List.flatMap_append,FormulaVertexTailFields.variable_fields,
    FormulaVertexTailFields.rail_fields,FormulaVertexTailFields.clause_fields]

def frame (v r L V C f g : Nat) : Fin 22 → Tape :=
  FormulaChangingFrame.extend (FormulaAllRailTails.frame v r L V C (regTape f)) (regTape g)

theorem parked (v r L V C f g : Nat) : ∀ t, Parked (frame v r L V C f g t) :=
  FormulaChangingFrame.parked _ _ (FormulaAllRailTails.parked _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _)

def machine (right : Bool) (ordinary merged : FormulaCoefficientPlan.Plan) : TM 22 :=
  seqTM (placeWorkTM 0 1 (FormulaAllVariableTails.machine right ordinary merged))
    (seqTM (placeWorkTM 0 1 (FormulaAllRailTails.prepared right ordinary))
      (FormulaAllClauseTails.machine right ordinary))

def railBudget (φ : SAT.CNF) : Nat :=
  2*(varCount φ)^2+11*varCount φ+13+
    varCount φ*(2*FormulaRailTailReentrant.budget φ+2*varCount φ+8)+(varCount φ+2)

def budget (φ : SAT.CNF) : Nat := FormulaAllVariableTails.budget φ+railBudget φ+FormulaAllClauseTails.budget φ+2

theorem canonical_hoare (φ : SAT.CNF) (right : Bool)
    (r : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ)) (v f g : Nat) (ys : List Bool)
    (hv : v ≤ cap φ) (hf : f ≤ cap φ) (hg : g ≤ cap φ) :
    (machine right (choose right (tag r) none none) (choose right (tag r) none (some false))).HoareTime
      (EmitPred (word φ.encode) (frame v (index r) (levels φ) (varCount φ) φ.length f g) ys)
      (EmitPred (word φ.encode) (frame (varCount φ) (index r) (levels φ) (varCount φ) φ.length
        (varCount φ) φ.length) (ys ++ bits φ right r)) (budget φ) := by
  have hV : varCount φ ≤ cap φ := by
    have h := (FormulaEnumeration.parameter_bounds φ).2.1
    unfold cap; nlinarith
  have h0 := FormulaAllVariableTails.canonical_hoare φ right r v f ys hv hf
  have h0' := FormulaChangingFrame.append_hoare _ _ _ _ (regTape g) _ _ _
    (FormulaAllRailTails.parked _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _) h0
  let zs := ys ++ FormulaAllVariableTails.bits φ right r
  have h1 := (FormulaAllRailTails.prepared_hoare φ right r (varCount φ) (varCount φ) zs).mono_bound
    (show _ ≤ railBudget φ by unfold railBudget; omega)
  have h1' := FormulaChangingFrame.append_hoare _ _ _ _ (regTape g) _ _ _
    (FormulaAllRailTails.parked _ _ _ _ _ _ (parked_regTape _)) (parked_regTape _) h1
  let ts := zs ++ FormulaAllRailTails.bits φ right r (varCount φ)
  have h2 := FormulaAllClauseTails.canonical_hoare φ right r (varCount φ) g ts hV hg
  have h12 := seqTM_hoareTime _ _ h1' (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _) _) h2
  have h := seqTM_hoareTime _ _ h0' (emitPred_transition (word_parked _) (parked _ _ _ _ _ _ _) _) h12
  have he : ts ++ FormulaAllClauseTails.bits φ right r = ys ++ bits φ right r := by
    unfold ts zs
    rw [List.append_assoc,List.append_assoc,← List.append_assoc
      (FormulaAllVariableTails.bits φ right r) (FormulaAllRailTails.bits φ right r (varCount φ)),bits_eq]
  rw [he] at h
  exact h.mono_bound (by unfold budget; omega)

end UnconstrainedPACDetection.FormulaExternalTailPhase

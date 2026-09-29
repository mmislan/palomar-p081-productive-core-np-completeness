module

public import proofs.UnconstrainedPACDetection.FormulaVariablePair
public import proofs.UnconstrainedPACDetection.FormulaNormalization

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchPair
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)
open FormulaCoefficientPlan (choose tag index)
open FormulaPairExecution (tailMeaning headMeaning)
open FormulaEqualityPair (bank)

inductive Mode where
  | localEdge | forward | backward | reject
  deriving DecidableEq

instance : Fintype Mode where
  elems := {.localEdge, .forward, .backward, .reject}
  complete := fun q => by cases q <;> simp

def mode (a b : ControlSwitch.V) : Mode :=
  if b ∈ ControlSwitch.next a then .localEdge else
  if a=5 ∧ b=1 then .forward else
  if a=4 ∧ b=0 then .backward else .reject

def first (m : Mode) (i j : Nat) := if m = .backward then j else i
def second (m : Mode) (i j : Nat) := if m = .backward then i else j
def enabled (m : Mode) : Bool := decide (m ≠ .reject)
def offset (m : Mode) : Bool := decide (m ≠ .localEdge)

theorem admission (φ : SAT.CNF) (i j : Fin (FormulaWiring.levels φ)) (a b : ControlSwitch.V) :
    FormulaWiring.adjacency φ (SwitchStack.sw i a) (SwitchStack.sw j b) ↔
      enabled (mode a b)=true ∧
      first (mode a b) i.val j.val + (if offset (mode a b) then 1 else 0) =
        second (mode a b) i.val j.val ∧ 0+(if false then 1 else 0)=0 := by
  have base : FormulaWiring.adjacency φ (SwitchStack.sw i a) (SwitchStack.sw j b) ↔
      (i=j ∧ b ∈ ControlSwitch.next a) ∨ (a=5 ∧ b=1 ∧ j.val=i.val+1) ∨
        (a=4 ∧ b=0 ∧ i.val=j.val+1) := by
    simp [FormulaWiring.adjacency,SwitchStack.Edge,SwitchStack.sw,FormulaWiring.DataWire]
  rw [base]
  by_cases hl : b ∈ ControlSwitch.next a
  · have h5 : a ≠ 5 := by intro h; subst a; simp [ControlSwitch.next,ControlSwitch.edges] at hl
    have h4 : a ≠ 4 := by intro h; subst a; simp [ControlSwitch.next,ControlSwitch.edges] at hl
    rw [show mode a b = .localEdge by simp only [mode,ite_eq_left hl]]
    simpa [hl,h5,h4,enabled,offset,first,second] using
      (Fin.ext_iff : i=j ↔ i.val=j.val)
  · by_cases hf : a=5 ∧ b=1
    · rcases hf with ⟨rfl,rfl⟩
      simp [mode,hl,first,second,enabled,offset,eq_comm]
    · by_cases hb : a=4 ∧ b=0
      · rcases hb with ⟨rfl,rfl⟩
        simp [mode,hl,first,second,enabled,offset,eq_comm]
      · rw [show mode a b = .reject by simp only [mode,ite_eq_right hl,ite_eq_right hf,ite_eq_right hb]]
        simp [enabled,offset,first,second]
        aesop

theorem canonical_hoare (φ : SAT.CNF) (i j : Fin (FormulaWiring.levels φ))
    (u v : ControlSwitch.V) (right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (ha : tailMeaning φ a = SwitchStack.sw i u)
    (hb : headMeaning φ b = SwitchStack.sw j v) (ys : List Bool) :
    (FormulaVariablePair.machine (enabled (mode u v)) (offset (mode u v)) false right
      (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred (word φ.encode)
        (bank (first (mode u v) i.val j.val) (second (mode u v) i.val j.val) 0 0
          (index r) (index a) (index b)) ys)
      (EmitPred (word φ.encode)
        (bank (first (mode u v) i.val j.val) (second (mode u v) i.val j.val) 0 0
          (index r) (index a) (index b))
        (ys ++ if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
          (FormulaIndexedGraph.terminals φ) (a,b) then BinaryFields.encodeField
            (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits else []))
      (4*first (mode u v) i.val j.val+
        3*max (first (mode u v) i.val j.val+1) (second (mode u v) i.val j.val)+
        3*max (index r) (if right then index b else index a)+100) := by
  have he : FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,b) ↔
      FormulaWiring.adjacency φ (SwitchStack.sw i u) (SwitchStack.sw j v) := by
    change FormulaWiring.adjacency φ (tailMeaning φ a) (headMeaning φ b) ∧
      tailVertex a ≠ headVertex b ↔ _
    constructor
    · intro h; simpa only [ha,hb] using h.1
    · intro h
      refine ⟨by simpa only [ha,hb] using h,?_⟩
      intro hphys
      have hh := congrArg (fun q => FormulaIndexedGraph.vertexEquiv φ
        (MarkedGraph.decode (FormulaIndexedGraph.terminals φ) q)) hphys
      change tailMeaning φ a = headMeaning φ b at hh
      rw [ha,hb] at hh
      rw [hh] at h
      exact FormulaNormalization.no_loop φ _ h
  have h := FormulaVariablePair.canonical φ (enabled (mode u v)) (offset (mode u v)) false
    right (first (mode u v) i.val j.val) (second (mode u v) i.val j.val) 0 0 r a b
    (he.trans (admission φ i j u v)) ys
  exact h.mono_bound (by simp; omega)

inductive Family where
  | switchSwitch | switchVariable | switchRail | switchClause
  | variableRail | railRail | railVariable | variableClause | clauseSwitch | reject
  deriving DecidableEq

instance : Fintype Family where
  elems := {.switchSwitch, .switchVariable, .switchRail, .switchClause,
    .variableRail, .railRail, .railVariable, .variableClause, .clauseSwitch, .reject}
  complete := fun q => by cases q <;> simp

def family {φ : SAT.CNF} : FormulaWiring.Vertex φ → FormulaWiring.Vertex φ → Family
  | .inl _, .inl _ => .switchSwitch
  | .inl _, .inr (.var _) => .switchVariable
  | .inl _, .inr (.rail _ _ _) => .switchRail
  | .inl _, .inr (.clause _) => .switchClause
  | .inr (.var _), .inr (.rail _ _ _) => .variableRail
  | .inr (.rail _ _ _), .inr (.rail _ _ _) => .railRail
  | .inr (.rail _ _ _), .inr (.var _) => .railVariable
  | .inr (.var _), .inr (.clause _) => .variableClause
  | .inr (.clause _), .inl _ => .clauseSwitch
  | _, _ => .reject

/-- Rail-to-switch is separated from the finite-table families. -/
def railToSwitch {φ : SAT.CNF} : FormulaWiring.Vertex φ → FormulaWiring.Vertex φ → Bool
  | .inr (.rail _ _ _), .inl _ => true
  | _, _ => false

theorem remaining_rejected (φ : SAT.CNF) (x y : FormulaWiring.Vertex φ)
    (hf : family x y = .reject) (hr : railToSwitch x y = false) :
    ¬FormulaWiring.adjacency φ x y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => simp_all [family]
    | inr y => cases y <;> simp_all [family]
  | inr x =>
    cases y with
    | inl y => cases x <;>
        simp_all [family,railToSwitch,FormulaWiring.adjacency,SwitchStack.Edge,SwitchStack.sw,FormulaWiring.DataWire]
    | inr y => cases x <;> cases y <;>
        simp_all [family,FormulaWiring.adjacency,SwitchStack.Edge,FormulaWiring.DataWire]

theorem rejected_hoare {n : Nat} (φ : SAT.CNF) (right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal (FormulaIndexedGraph.terminals φ))
    (hf : family (tailMeaning φ a) (headMeaning φ b) = .reject)
    (hr : railToSwitch (tailMeaning φ a) (headMeaning φ b) = false)
    (w : Fin n → Tape) (hw : ∀ j, Parked (w j)) (ys : List Bool) :
    (emitBitsTM ([] : List Bool)).HoareTime (EmitPred (word φ.encode) w ys)
      (EmitPred (word φ.encode) w
        (ys ++ if FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
          (FormulaIndexedGraph.terminals φ) (a,b) then BinaryFields.encodeField
            (FormulaOrderedTable.coefficient (FormulaIndexedGraph.terminals φ) right r (a,b)).bits else [])) 0 := by
  have hn : ¬FiniteMarkedSource.arcPredicate (FormulaIndexedGraph.edge φ)
      (FormulaIndexedGraph.terminals φ) (a,b) := fun h => remaining_rejected φ _ _ hf hr h.1
  unfold EmitPred
  simpa only [ite_eq_right hn,List.append_nil,List.length_nil] using emitBitsTM_hoareTime ([] : List Bool)
    (word φ.encode) w ys (word_parked _) hw

end UnconstrainedPACDetection.FormulaSwitchPair

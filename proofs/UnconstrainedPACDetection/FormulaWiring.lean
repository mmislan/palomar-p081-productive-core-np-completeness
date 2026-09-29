module

public import proofs.UnconstrainedPACDetection.ResidualSuffix
public import proofs.UnconstrainedPACDetection.SATInputBounds

@[expose] public section

namespace UnconstrainedPACDetection.FormulaWiring
open Complexity.SAT ControlSwitch SwitchStack

/-- Clause-indexed literal occurrences; repeats retain distinct switch identities. -/
def occurrences (φ : CNF) : List (Nat × Lit) :=
  φ.zipIdx.flatMap fun c => c.1.map fun l => (c.2,l)

/-- One unused final switch makes the stack positive even for an empty CNF. -/
def levels (φ : CNF) : Nat := (occurrences φ).length + 1
theorem levels_pos (φ : CNF) : 0 < levels φ := Nat.zero_lt_succ _
def varCount (φ : CNF) : Nat := φ.maxVar + 1

inductive External (φ : CNF) where
  | var (v : Fin (varCount φ + 1))
  | rail (v : Fin (varCount φ)) (value : Bool) (cursor : Fin (levels φ + 1))
  | clause (c : Fin (φ.length + 1))
  deriving DecidableEq, Fintype

abbrev Vertex (φ : CNF) := Node (levels φ) (External φ)
instance vertexDecidableEq (φ : CNF) : DecidableEq (Vertex φ) := by
  unfold Vertex Node
  infer_instance
def lookup (φ : CNF) (i : Fin (levels φ)) : Option (Nat × Lit) :=
  (occurrences φ)[i.val]?
def blocked (φ : CNF) (i : Fin (levels φ)) (v : Fin (varCount φ)) (value : Bool) : Bool :=
  match lookup φ i with
  | none => false
  | some (_,l) => l.var == v.val && l.sign != value

/-- Exact logical wiring. All other pairs are false. -/
def DataWire (φ : CNF) : Vertex φ → Vertex φ → Prop
  | Sum.inl (i,a), Sum.inr (.var v) =>
      a = 5 ∧ i.val + 1 = levels φ ∧ v.val = 0
  | Sum.inr (.var v), Sum.inr (.rail w _ j) => v.val = w.val ∧ j.val = 0
  | Sum.inr (.rail v b j), Sum.inr (.rail w c k) =>
      v = w ∧ b = c ∧ ∃ hj : j.val < levels φ,
        k.val = j.val + 1 ∧ blocked φ ⟨j.val,hj⟩ v b = false
  | Sum.inr (.rail v b j), Sum.inl (i,a) =>
      a = 3 ∧ j.val = i.val ∧ blocked φ i v b = true
  | Sum.inl (i,a), Sum.inr (.rail v b j) =>
      a = 7 ∧ j.val = i.val + 1 ∧ blocked φ i v b = true
  | Sum.inr (.rail v _ j), Sum.inr (.var w) =>
      j.val = levels φ ∧ w.val = v.val + 1
  | Sum.inr (.var v), Sum.inr (.clause c) => v.val = varCount φ ∧ c.val = 0
  | Sum.inr (.clause c), Sum.inl (i,a) =>
      a = 2 ∧ ∃ l, lookup φ i = some (c.val,l)
  | Sum.inl (i,a), Sum.inr (.clause c) =>
      a = 6 ∧ ∃ j l, lookup φ i = some (j,l) ∧ c.val = j+1
  | _, _ => False

/-- The formula graph is the stack graph itself, instantiated with exact wiring. -/
def adjacency (φ : CNF) := Edge (DataWire φ)
def sourceP (φ : CNF) : Vertex φ := sw ⟨0,levels_pos φ⟩ 1
def sourceQ (φ : CNF) : Vertex φ := sw ⟨levels φ-1,by have := levels_pos φ; omega⟩ 0
def sinkQ (φ : CNF) : Vertex φ := sw ⟨0,levels_pos φ⟩ 4
def sinkP (φ : CNF) : Vertex φ := Sum.inr (.clause ⟨φ.length,by omega⟩)

structure Accepted (φ : CNF) (p q : List (Vertex φ)) : Prop where
  p_chain : p.IsChain (adjacency φ)
  q_chain : q.IsChain (adjacency φ)
  p_nodup : p.Nodup
  q_nodup : q.Nodup
  disjoint : p.Disjoint q
  p_start : p.head? = some (sourceP φ)
  p_finish : p.getLast? = some (sinkP φ)
  q_start : q.head? = some (sourceQ φ)
  q_finish : q.getLast? = some (sinkQ φ)

theorem accepted_control_ports (φ : CNF) {p q : List (Vertex φ)} (h : Accepted φ p q) :
    ∀ i : Fin (levels φ), sw i 1 ∈ p ∧ sw i 5 ∈ p ∧ sw i 0 ∈ q ∧ sw i 4 ∈ q :=
  all_control_ports (levels_pos φ) (DataWire φ) h.p_chain h.q_chain h.p_nodup h.q_nodup
    h.disjoint h.p_start h.p_finish h.q_start h.q_finish

theorem accepted_suffix_exclusive (φ : CNF) {p q : List (Vertex φ)} (h : Accepted φ p q) :
    ∃ pre suffix : List (Vertex φ),
      p = pre ++ [sw ⟨levels φ-1,by have := levels_pos φ; omega⟩ 5] ++ suffix ∧
      (∀ i : Fin (levels φ), ¬(sw i 2 ∈ suffix ∧ sw i 3 ∈ suffix)) :=
  ResidualSuffix.logical_suffix_exclusive (levels_pos φ) (DataWire φ)
    h.p_chain h.q_chain h.p_nodup h.q_nodup h.disjoint h.p_start h.p_finish h.q_start h.q_finish

theorem dummy_lookup (φ : CNF) : lookup φ ⟨(occurrences φ).length,by simp [levels]⟩ = none := by
  simp [lookup]

theorem dummy_unblocked (φ : CNF) (v : Fin (varCount φ)) (b : Bool) :
    blocked φ ⟨(occurrences φ).length,by simp [levels]⟩ v b = false := by
  simp [blocked,dummy_lookup]

def emptyP : List (Vertex []) :=
  (leftDown.map fun a => sw ⟨0,by decide⟩ a) ++
  [Sum.inr (.var ⟨0,by decide⟩), Sum.inr (.rail ⟨0,by decide⟩ false ⟨0,by decide⟩),
   Sum.inr (.rail ⟨0,by decide⟩ false ⟨1,by decide⟩),
   Sum.inr (.var ⟨1,by decide⟩), Sum.inr (.clause ⟨0,by decide⟩)]
def emptyQ : List (Vertex []) := leftUp.map fun a => sw ⟨0,by decide⟩ a

theorem empty_accepted : Accepted [] emptyP emptyQ := by
  constructor
  · repeat' apply List.IsChain.cons_cons
    all_goals first | exact List.IsChain.singleton _ | norm_num [adjacency,Edge,DataWire,sw,next,edges,blocked,lookup,occurrences,levels,varCount]
  · repeat' apply List.IsChain.cons_cons
    all_goals first | exact List.IsChain.singleton _ | norm_num [adjacency,Edge,DataWire,sw,next,edges,blocked,lookup,occurrences,levels,varCount]
  · decide
  · decide
  · change ∀ v : Vertex [], v ∈ emptyP → v ∉ emptyQ
    simp [emptyP,emptyQ,leftDown,leftUp,sw]
  · rfl
  · rfl
  · rfl
  · rfl

theorem empty_clause_no_incoming (x : Vertex [[]]) : ¬adjacency [[]] x (sinkP [[]]) := by
  cases x with
  | inl z =>
    obtain ⟨i,a⟩ := z
    simp [adjacency,Edge,sinkP,DataWire,lookup,occurrences,sw]
  | inr e =>
    cases e <;> simp [adjacency,Edge,sinkP,DataWire]

theorem empty_clause_rejected {p q : List (Vertex [[]])} : ¬Accepted [[]] p q := by
  intro h
  obtain ⟨x,hx,_⟩ := SwitchSegments.predecessor h.p_chain
    (SwitchSegments.last_mem h.p_finish) (by rw [h.p_start]; simp [sourceP,sinkP,sw])
  exact empty_clause_no_incoming x hx

end UnconstrainedPACDetection.FormulaWiring

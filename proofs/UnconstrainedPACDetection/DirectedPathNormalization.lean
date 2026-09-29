module

public import Mathlib.Tactic

@[expose] public section

namespace UnconstrainedPACDetection.DirectedPathNormalization

/-- A positive-length simple directed path in an arbitrary adjacency relation. -/
structure SimplePath {X : Type*} (A : X → X → Prop) (s t : X) where
  length : ℕ
  positive : 0 < length
  vertex : Fin (length + 1) → X
  injective : Function.Injective vertex
  start : vertex ⟨0, by omega⟩ = s
  finish : vertex ⟨length, by omega⟩ = t
  edge : ∀ i : Fin length, A (vertex i.castSucc) (vertex i.succ)

namespace SimplePath

variable {X : Type*} {A B : X → X → Prop} {s t a b : X}

def vertices (P : SimplePath A s t) : Set X := Set.range P.vertex

theorem edge_ne (P : SimplePath A s t) (i : Fin P.length) :
    P.vertex i.castSucc ≠ P.vertex i.succ := by
  intro h
  have hi := congrArg Fin.val (P.injective h)
  change i.1 = i.1 + 1 at hi
  omega

theorem edge_tail_ne_finish (P : SimplePath A s t) (i : Fin P.length) :
    P.vertex i.castSucc ≠ t := by
  intro h
  have hi := congrArg Fin.val (P.injective (h.trans P.finish.symm))
  change i.1 = P.length at hi
  omega

theorem edge_head_ne_start (P : SimplePath A s t) (i : Fin P.length) :
    P.vertex i.succ ≠ s := by
  intro h
  have hi := congrArg Fin.val (P.injective (h.trans P.start.symm))
  change i.1 + 1 = 0 at hi
  omega

theorem avoids_other_start (P : SimplePath A s t) (Q : SimplePath A a b)
    (hd : Disjoint P.vertices Q.vertices) (i : Fin (P.length + 1)) :
    P.vertex i ≠ a := by
  intro h
  apply Set.disjoint_left.mp hd (show P.vertex i ∈ P.vertices from ⟨i, rfl⟩)
  exact ⟨⟨0, by omega⟩, Q.start.trans h.symm⟩

theorem avoids_other_finish (P : SimplePath A s t) (Q : SimplePath A a b)
    (hd : Disjoint P.vertices Q.vertices) (i : Fin (P.length + 1)) :
    P.vertex i ≠ b := by
  intro h
  apply Set.disjoint_left.mp hd (show P.vertex i ∈ P.vertices from ⟨i, rfl⟩)
  exact ⟨⟨Q.length, by omega⟩, Q.finish.trans h.symm⟩

def changeEdges (P : SimplePath A s t)
    (h : ∀ i : Fin P.length, B (P.vertex i.castSucc) (P.vertex i.succ)) :
    SimplePath B s t where
  length := P.length
  positive := P.positive
  vertex := P.vertex
  injective := P.injective
  start := P.start
  finish := P.finish
  edge := h

end SimplePath

def pruned {X : Type*} (A : X → X → Prop) (s1 s2 t1 t2 : X) (u v : X) : Prop :=
  A u v ∧ u ≠ v ∧ u ≠ t1 ∧ u ≠ t2 ∧ v ≠ s1 ∧ v ≠ s2

def Linkage {X : Type*} (A : X → X → Prop) (s1 s2 t1 t2 : X) : Prop :=
  ∃ (P : SimplePath A s1 t1) (Q : SimplePath A s2 t2), Disjoint P.vertices Q.vertices

/-- Deleting loops, incoming source arcs and outgoing sink arcs preserves
the pair language. No analogous single-path preservation is assumed. -/
theorem linkage_pruned_iff {X : Type*} (A : X → X → Prop) (s1 s2 t1 t2 : X) :
    Linkage (pruned A s1 s2 t1 t2) s1 s2 t1 t2 ↔ Linkage A s1 s2 t1 t2 := by
  constructor
  · rintro ⟨P, Q, hd⟩
    exact ⟨P.changeEdges (fun i => (P.edge i).1),
      Q.changeEdges (fun i => (Q.edge i).1), hd⟩
  · rintro ⟨P, Q, hd⟩
    have hp : ∀ i : Fin P.length, pruned A s1 s2 t1 t2 (P.vertex i.castSucc) (P.vertex i.succ) := by
      intro i
      exact ⟨P.edge i, P.edge_ne i, P.edge_tail_ne_finish i,
        P.avoids_other_finish Q hd i.castSucc, P.edge_head_ne_start i,
        P.avoids_other_start Q hd i.succ⟩
    have hq : ∀ i : Fin Q.length, pruned A s1 s2 t1 t2 (Q.vertex i.castSucc) (Q.vertex i.succ) := by
      intro i
      exact ⟨Q.edge i, Q.edge_ne i, Q.avoids_other_finish P hd.symm i.castSucc,
        Q.edge_tail_ne_finish i, Q.avoids_other_start P hd.symm i.succ,
        Q.edge_head_ne_start i⟩
    exact ⟨P.changeEdges hp, Q.changeEdges hq, hd⟩

end UnconstrainedPACDetection.DirectedPathNormalization

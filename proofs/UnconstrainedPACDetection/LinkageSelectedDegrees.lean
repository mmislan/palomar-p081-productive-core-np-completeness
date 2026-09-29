module

public import proofs.UnconstrainedPACDetection.LinkageLocalSigns
public import proofs.UnconstrainedPACDetection.DegreeTwoSignedNeighbors

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

theorem internal_unique_arcs {V E : Type*} [DecidableEq V] [Fintype E]
    (D : Network V E) (v : V)
    (hdegree : (Finset.univ.filter (fun e => matrix D (Sum.inr v) e ≠ 0)).card ≤ 2)
    (hmixed : (∃ e, matrix D (Sum.inr v) e < 0) ∧
      ∃ e, 0 < matrix D (Sum.inr v) e) :
    (∃! e, D.tail e = Sum.inr v) ∧ ∃! e, D.head e = Sum.inr v := by
  obtain ⟨hn, hp⟩ := DegreeTwoSignedNeighbors.unique_signs _ hdegree hmixed
  exact ⟨(existsUnique_congr (fun e => (local_signs D e v).1.1)).mp hn,
    (existsUnique_congr (fun e => (local_signs D e v).1.2)).mp hp⟩

theorem source_unique_arcs {V E : Type*} [DecidableEq V] [Fintype E]
    (D : Network V E)
    (hdegree : (Finset.univ.filter (fun e => matrix D (Sum.inl false) e ≠ 0)).card ≤ 2)
    (hmixed : (∃ e, matrix D (Sum.inl false) e < 0) ∧
      ∃ e, 0 < matrix D (Sum.inl false) e) :
    (∃! e, D.tail e = Sum.inl false) ∧ ∃! e, D.tail e = Sum.inl true := by
  obtain ⟨hn, hp⟩ := DegreeTwoSignedNeighbors.unique_signs _ hdegree hmixed
  exact ⟨(existsUnique_congr (fun e => (terminal_signs D e).1.1)).mp hn,
    (existsUnique_congr (fun e => (terminal_signs D e).1.2)).mp hp⟩

theorem sink_unique_arcs {V E : Type*} [DecidableEq V] [Fintype E]
    (D : Network V E)
    (hdegree : (Finset.univ.filter (fun e => matrix D (Sum.inl true) e ≠ 0)).card ≤ 2)
    (hmixed : (∃ e, matrix D (Sum.inl true) e < 0) ∧
      ∃ e, 0 < matrix D (Sum.inl true) e) :
    (∃! e, D.head e = Sum.inl false) ∧ ∃! e, D.head e = Sum.inl true := by
  obtain ⟨hn, hp⟩ := DegreeTwoSignedNeighbors.unique_signs _ hdegree hmixed
  exact ⟨(existsUnique_congr (fun e => (terminal_signs D e).2.1)).mp hn,
    (existsUnique_congr (fun e => (terminal_signs D e).2.2)).mp hp⟩

end UnconstrainedPACDetection.DirectedLinkageSource

module

public import proofs.UnconstrainedPACDetection.ExternalTrace

@[expose] public section

namespace UnconstrainedPACDetection.AcceptedTrace
open FormulaWiring LogicalTrace ExternalTrace SwitchStack ControlSwitch

def start (φ : Complexity.SAT.CNF) : External φ := .var ⟨0,Nat.zero_lt_succ _⟩
def finish (φ : Complexity.SAT.CNF) : External φ := .clause ⟨φ.length,Nat.lt_succ_self _⟩
def top (φ : Complexity.SAT.CNF) : Fin (levels φ) :=
  ⟨levels φ-1,by have := levels_pos φ; omega⟩

theorem top_exit (φ : Complexity.SAT.CNF) {x : Vertex φ}
    (h : adjacency φ (sw (top φ) 5) x) : x = Sum.inr (start φ) := by
  cases x with
  | inl z =>
    obtain ⟨j,a⟩ := z
    simp [adjacency,Edge,sw,DataWire,next,edges,top] at h
    have := j.isLt
    have := levels_pos φ
    omega
  | inr e =>
    cases e with
    | var v =>
      simp [adjacency,Edge,sw,DataWire] at h
      have hv : v = ⟨0,Nat.zero_lt_succ _⟩ := h.2
      subst v
      rfl
    | rail v b j => simp [adjacency,Edge,sw,DataWire] at h
    | clause c => simp [adjacency,Edge,sw,DataWire] at h

/-- The observed trace and exclusivity refer to the same actual suffix of the
accepted first path. No control visitation or residual behavior is assumed. -/
theorem accepted_trace (φ : Complexity.SAT.CNF) {p q : List (Vertex φ)}
    (h : Accepted φ p q) :
    ∃ pre tail, ∃ trace : List (External φ),
      p = pre ++ [sw (top φ) 5] ++ (Sum.inr (start φ) :: tail) ∧
      trace.head? = some (start φ) ∧ trace.getLast? = some (finish φ) ∧
      trace.IsChain (ObservedStep φ (Sum.inr (start φ) :: tail)) ∧
      (∀ i : Fin (levels φ), ¬(sw i 2 ∈ Sum.inr (start φ) :: tail ∧
        sw i 3 ∈ Sum.inr (start φ) :: tail)) := by
  obtain ⟨pre,suffix,heq,hcontrols⟩ := ResidualSuffix.suffix_has_controls
    (levels_pos φ) (DataWire φ) h.p_chain h.q_chain h.p_nodup h.q_nodup
    h.disjoint h.p_start h.p_finish h.q_start h.q_finish
  change p = pre ++ [sw (top φ) 5] ++ suffix at heq
  have hc : (pre ++ [sw (top φ) 5] ++ suffix).IsChain (adjacency φ) := heq ▸ h.p_chain
  have hn : suffix.Nodup := (heq ▸ h.p_nodup).of_append_right
  have hs : suffix.IsChain (adjacency φ) := (List.isChain_append.mp hc).2.1
  have he : suffix.getLast? = some (Sum.inr (finish φ)) := by
    have hp := h.p_finish
    rw [heq] at hp
    cases suffix with
    | nil => simp [sinkP,sw] at hp
    | cons x xs => simpa [sinkP,finish] using hp
  cases suffix with
  | nil => simp at he
  | cons x tail =>
    have hx : adjacency φ (sw (top φ) 5) x :=
      (List.isChain_append.mp hc).2.2 _ (by simp) _ (by rfl)
    have hstart := top_exit φ hx
    subst x
    have hcon : ∀ i : Fin (levels φ), ∃ up down,
        Path 0 4 up ∧ Path 1 5 down ∧ up.Disjoint down ∧
        ∀ v ∈ up ++ down, sw i v ∉ Sum.inr (start φ) :: tail := by
      intro i
      obtain ⟨up,down,hu,hd,hud,_,_,hav⟩ := hcontrols i
      exact ⟨up,down,hu,hd,hud,hav⟩
    obtain ⟨trace,hh,hl,hchain⟩ := trace_exists φ (start φ) tail (finish φ) hs hn he hcon
    refine ⟨pre,tail,trace,heq,hh,hl,hchain,?_⟩
    intro i ⟨hleft,hright⟩
    obtain ⟨up,down,hu,hd,hud,hav⟩ := hcon i
    exact ResidualSuffix.data_inputs_exclusive (DataWire φ) i hs hn he hu hd hud hav hleft hright

end UnconstrainedPACDetection.AcceptedTrace

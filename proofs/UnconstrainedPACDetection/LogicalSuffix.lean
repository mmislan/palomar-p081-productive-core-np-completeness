module

public import proofs.UnconstrainedPACDetection.SwitchStack

@[expose] public section

namespace UnconstrainedPACDetection.LogicalSuffix
open ControlSwitch SwitchSegments SwitchStack

/-- A path stopped at D of level k already contains B and D of every lower level. -/
theorem controls_before_exit {n : Nat} {X : Type*} (hn : 0 < n)
    (W : Node n X → Node n X → Prop) (k : Fin n) {p q : List (Node n X)}
    (hp : p.IsChain (Edge W)) (hq : q.IsChain (Edge W))
    (hpn : p.Nodup) (hqn : q.Nodup) (hd : p.Disjoint q)
    (hps : p.head? = some (sw ⟨0,hn⟩ 1)) (hpe : p.getLast? = some (sw k 5))
    (hqs : q.head? = some (sw ⟨n-1,by omega⟩ 0))
    (hqe : q.getLast? = some (sw ⟨0,hn⟩ 4)) :
    ∀ i : Fin n, i.val ≤ k.val → sw i 1 ∈ p ∧ sw i 5 ∈ p := by
  have end_ok (i : Fin n) (b : V) (h : p.getLast? = some (sw i b)) : output b := by
    rw [hpe] at h
    simp [sw] at h
    simp [output,← h.2]
  have start_ok (i : Fin n) (a : V) (h : q.head? = some (sw i a)) : input a := by
    rw [hqs] at h
    simp [sw] at h
    simp [input,← h.2]
  have pairs : ∀ j (hj : j < n), j ≤ k.val → sw ⟨j,hj⟩ 1 ∈ p ∧ sw ⟨j,hj⟩ 4 ∈ q := by
    intro j
    induction j with
    | zero => intro hj _; exact ⟨head_mem hps,last_mem hqe⟩
    | succ j ih =>
      intro hj hle
      have hj' : j < n := by omega
      obtain ⟨hb,ha⟩ := ih hj' (by omega)
      obtain ⟨hD,hC⟩ := force_one W ⟨j,hj'⟩ hp hq hpn hqn hd
        (end_ok _) (start_ok _) hb ha
      obtain ⟨y,hy,hym⟩ := successor hp hD (by
        rw [hpe]
        intro h
        simp [sw] at h
        have he : k.val = j := congrArg Fin.val h
        omega)
      obtain ⟨z,hz,hzm⟩ := predecessor hq hC (by
        rw [hqs]
        intro h
        simp [sw] at h
        omega)
      exact ⟨next_D W ⟨j,hj'⟩ hj hy ▸ hym,previous_C W ⟨j,hj'⟩ hj hz ▸ hzm⟩
  intro i hi
  obtain ⟨hb,ha⟩ := pairs i.val i.isLt hi
  exact ⟨hb,(force_one W i hp hq hpn hqn hd (end_ok _) (start_ok _) hb ha).1⟩

/-- Exact cut at the top D. The logical suffix contains no control port. -/
theorem logical_suffix_avoids_controls {n : Nat} {X : Type*} (hn : 0 < n)
    (W : Node n X → Node n X → Prop) {p q : List (Node n X)} {t : X}
    (hp : p.IsChain (Edge W)) (hq : q.IsChain (Edge W))
    (hpn : p.Nodup) (hqn : q.Nodup) (hd : p.Disjoint q)
    (hps : p.head? = some (sw ⟨0,hn⟩ 1)) (hpe : p.getLast? = some (Sum.inr t))
    (hqs : q.head? = some (sw ⟨n-1,by omega⟩ 0))
    (hqe : q.getLast? = some (sw ⟨0,hn⟩ 4)) :
    ∃ pre suffix : List (Node n X),
      p = pre ++ [sw ⟨n-1,by omega⟩ 5] ++ suffix ∧
      (∀ i : Fin n, sw i 1 ∈ pre ++ [sw ⟨n-1,by omega⟩ 5] ∧
        sw i 5 ∈ pre ++ [sw ⟨n-1,by omega⟩ 5]) ∧
      (∀ i : Fin n, ∀ a ∈ ([0,1,4,5] : List V), sw i a ∉ suffix) := by
  have hall := all_control_ports hn W hp hq hpn hqn hd hps hpe hqs hqe
  obtain ⟨pre,suffix,heq⟩ := List.mem_iff_append.mp (hall ⟨n-1,by omega⟩).2.1
  subst p
  let ctrl := pre ++ [sw (X := X) ⟨n-1,by omega⟩ 5]
  have hprefix : ctrl.IsChain (Edge W) := (List.isChain_split.mp hp).1
  have hsplit : pre ++ sw (X := X) ⟨n-1,by omega⟩ 5 :: suffix = ctrl ++ suffix := by
    simp [ctrl]
  have hprefixn : ctrl.Nodup := (hsplit ▸ hpn).of_append_left
  have hprefixd : ctrl.Disjoint q := by
    intro x hx hq'
    apply hd _ hq'
    rw [hsplit]
    exact List.mem_append_left _ hx
  have hstart : ctrl.head? = some (sw ⟨0,hn⟩ 1) := by
    cases pre <;> simpa [ctrl] using hps
  have hlast : ctrl.getLast? = some (sw ⟨n-1,by omega⟩ 5) := by simp [ctrl]
  have hports := controls_before_exit hn W ⟨n-1,by omega⟩ hprefix hq
    hprefixn hqn hprefixd hstart hlast hqs hqe
  refine ⟨pre,suffix,by simp,?_,?_⟩
  · intro i
    exact hports i (by change i.val ≤ n-1; omega)
  · intro i a ha hm
    have hmem : sw i a ∈ pre ++ sw ⟨n-1,by omega⟩ 5 :: suffix :=
      List.mem_append_right _ (List.mem_cons_of_mem _ hm)
    have hnsep : ctrl.Disjoint suffix := by
      intro x hx hy
      exact (List.nodup_append.mp (hsplit ▸ hpn)).2.2 x hx x hy rfl
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact hd hmem (hall i).2.2.1
    · exact hnsep ((hports i (by change i.val ≤ n-1; omega)).1) hm
    · exact hd hmem (hall i).2.2.2
    · exact hnsep ((hports i (by change i.val ≤ n-1; omega)).2) hm

end UnconstrainedPACDetection.LogicalSuffix

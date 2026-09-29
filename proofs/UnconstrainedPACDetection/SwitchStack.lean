module

public import proofs.UnconstrainedPACDetection.SwitchSegments

@[expose] public section

namespace UnconstrainedPACDetection.SwitchStack

open ControlSwitch SwitchSegments

abbrev Node (n : Nat) (X : Type*) := (Fin n × V) ⊕ X
def sw {n : Nat} {X : Type*} (i : Fin n) (a : V) : Node n X := Sum.inl (i,a)
def input (a : V) : Prop := a ∈ ([0,1,2,3] : List V)
def output (a : V) : Prop := a ∈ ([4,5,6,7] : List V)

/-- Internal switch arcs and compulsory neighboring control arcs, with arbitrary
data wiring restricted to the data ports. Only the top D can exit to the exterior. -/
def Edge {n : Nat} {X : Type*} (W : Node n X → Node n X → Prop) :
    Node n X → Node n X → Prop
  | Sum.inl (i,a), Sum.inl (j,b) =>
      (i = j ∧ b ∈ next a) ∨ (a = 5 ∧ b = 1 ∧ j.val = i.val+1) ∨
      (a = 4 ∧ b = 0 ∧ i.val = j.val+1) ∨
      ((a = 6 ∨ a = 7) ∧ (b = 2 ∨ b = 3) ∧ W (sw i a) (sw j b))
  | Sum.inl (i,a), Sum.inr y =>
      ((a = 5 ∧ i.val+1 = n) ∨ a = 6 ∨ a = 7) ∧ W (sw i a) (Sum.inr y)
  | Sum.inr x, Sum.inl (j,b) => (b = 2 ∨ b = 3) ∧ W (Sum.inr x) (sw j b)
  | Sum.inr x, Sum.inr y => W (Sum.inr x) (Sum.inr y)

theorem restrict_out {n : Nat} {X : Type*} (W : Node n X → Node n X → Prop)
    (i : Fin n) (a b : V) (ha : ¬output a) (h : Edge W (sw i a) (sw i b)) :
    b ∈ next a := by
  simp only [Edge,sw] at h
  simp only [output,List.mem_cons] at ha
  aesop

theorem restrict_in {n : Nat} {X : Type*} (W : Node n X → Node n X → Prop)
    (i : Fin n) (a b : V) (ha : ¬input a) (h : Edge W (sw i b) (sw i a)) :
    a ∈ next b := by
  simp only [Edge,sw] at h
  simp only [input,List.mem_cons] at ha
  aesop

theorem exits {n : Nat} {X : Type*} (W : Node n X → Node n X → Prop)
    (i : Fin n) (a : V) (y : Node n X) (h : Edge W (sw i a) y)
    (hy : ∀ b, y ≠ sw i b) : output a := by
  cases y with
  | inl z =>
    obtain ⟨j,b⟩ := z
    have hne : i ≠ j := by intro hij; subst j; exact hy b rfl
    simp only [Edge,sw] at h
    simp only [output,List.mem_cons]
    aesop
  | inr x =>
    simp only [Edge,sw] at h
    simp only [output,List.mem_cons]
    aesop

theorem enters {n : Nat} {X : Type*} (W : Node n X → Node n X → Prop)
    (i : Fin n) (a : V) (y : Node n X) (h : Edge W y (sw i a))
    (hy : ∀ b, y ≠ sw i b) : input a := by
  cases y with
  | inl z =>
    obtain ⟨j,b⟩ := z
    have hne : j ≠ i := by intro hij; subst j; exact hy b rfl
    simp only [Edge,sw] at h
    simp only [input,List.mem_cons]
    aesop
  | inr x =>
    simp only [Edge,sw] at h
    simp only [input,List.mem_cons]
    aesop

theorem force_one {n : Nat} {X : Type*} (W : Node n X → Node n X → Prop)
    (i : Fin n) {p q : List (Node n X)}
    (hp : p.IsChain (Edge W)) (hq : q.IsChain (Edge W))
    (hpn : p.Nodup) (hqn : q.Nodup) (hd : p.Disjoint q)
    (hpe : ∀ b, p.getLast? = some (sw i b) → output b)
    (hqs : ∀ a, q.head? = some (sw i a) → input a)
    (hb : sw i 1 ∈ p) (ha : sw i 4 ∈ q) : sw i 5 ∈ p ∧ sw i 0 ∈ q := by
  obtain ⟨b,ps,hb',hps,hpsub⟩ := exit_path (sw i) (Edge W) output
    (restrict_out W i) (exits W i) hp hpn hpe hb
  obtain ⟨a,qs,ha',hqs',hqsub⟩ := entry_path (sw i) (Edge W) input
    (restrict_in W i) (enters W i) hq hqn hqs ha
  have hdis : qs.Disjoint ps := by
    intro v hvq hvp
    exact hd (hpsub v hvp) (hqsub v hvq)
  obtain ⟨rfl,rfl⟩ := control_ports ha' hb' hqs' hps hdis
  exact ⟨hpsub 5 (last_mem hps.2.1),hqsub 0 (head_mem hqs'.1)⟩

theorem next_D {n : Nat} {X : Type*} (W : Node n X → Node n X → Prop)
    (i : Fin n) (hi : i.val+1 < n) {y : Node n X} (h : Edge W (sw i 5) y) :
    y = sw ⟨i.val+1,hi⟩ 1 := by
  cases y with
  | inl z =>
    obtain ⟨j,b⟩ := z
    simp [Edge,sw,next,edges] at h
    obtain ⟨rfl,hj⟩ := h
    have hji : j = ⟨i.val+1,hi⟩ := Fin.ext hj
    simp [sw,hji]
  | inr x =>
    simp [Edge,sw] at h
    omega

theorem no_enter_C : ∀ a : V, 0 ∉ next a := by decide

theorem previous_C {n : Nat} {X : Type*} (W : Node n X → Node n X → Prop)
    (i : Fin n) (hi : i.val+1 < n) {y : Node n X} (h : Edge W y (sw i 0)) :
    y = sw ⟨i.val+1,hi⟩ 4 := by
  cases y with
  | inl z =>
    obtain ⟨j,b⟩ := z
    simp [Edge,sw,no_enter_C] at h
    obtain ⟨rfl,hj⟩ := h
    have hji : j = ⟨i.val+1,hi⟩ := Fin.ext hj
    simp [sw,hji]
  | inr x => simp [Edge,sw] at h

/-- Every accepted pair visits all four control ports at every stack level.
The arbitrary data wiring is not assumed to force any control visit. -/
theorem all_control_ports {n : Nat} {X : Type*} (hn : 0 < n)
    (W : Node n X → Node n X → Prop) {p q : List (Node n X)} {t : X}
    (hp : p.IsChain (Edge W)) (hq : q.IsChain (Edge W))
    (hpn : p.Nodup) (hqn : q.Nodup) (hd : p.Disjoint q)
    (hps : p.head? = some (sw ⟨0,hn⟩ 1)) (hpe : p.getLast? = some (Sum.inr t))
    (hqs : q.head? = some (sw ⟨n-1,by omega⟩ 0))
    (hqe : q.getLast? = some (sw ⟨0,hn⟩ 4)) :
    ∀ i : Fin n, sw i 1 ∈ p ∧ sw i 5 ∈ p ∧ sw i 0 ∈ q ∧ sw i 4 ∈ q := by
  have end_ok (i : Fin n) (b : V) (h : p.getLast? = some (sw i b)) : output b := by
    rw [hpe] at h
    simp [sw] at h
  have start_ok (i : Fin n) (a : V) (h : q.head? = some (sw i a)) : input a := by
    rw [hqs] at h
    simp [sw] at h
    simp [input,← h.2]
  have pairs : ∀ k (hk : k < n), sw ⟨k,hk⟩ 1 ∈ p ∧ sw ⟨k,hk⟩ 4 ∈ q := by
    intro k
    induction k with
    | zero => intro hk; exact ⟨head_mem hps,last_mem hqe⟩
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      obtain ⟨hb,ha⟩ := ih hk'
      obtain ⟨hD,hC⟩ := force_one W ⟨k,hk'⟩ hp hq hpn hqn hd
        (end_ok _) (start_ok _) hb ha
      obtain ⟨y,hy,hym⟩ := successor hp hD (by simp [hpe,sw])
      have hy' := next_D W ⟨k,hk'⟩ hk hy
      obtain ⟨z,hz,hzm⟩ := predecessor hq hC (by
        rw [hqs]
        intro h
        have he : n-1 = k := congrArg (fun o => o.map (fun x =>
          match x with | Sum.inl v => v.1.val | Sum.inr _ => 0)) h |> Option.some.inj
        omega)
      have hz' := previous_C W ⟨k,hk'⟩ hk hz
      exact ⟨hy' ▸ hym,hz' ▸ hzm⟩
  intro i
  obtain ⟨hb,ha⟩ := pairs i.val i.isLt
  obtain ⟨hD,hC⟩ := force_one W i hp hq hpn hqn hd (end_ok _) (start_ok _) hb ha
  exact ⟨hb,hD,hC,ha⟩

end UnconstrainedPACDetection.SwitchStack

module

public import proofs.UnconstrainedPACDetection.AcceptedTrace

@[expose] public section

namespace UnconstrainedPACDetection.VariableAssignment
open FormulaWiring LogicalTrace ExternalTrace AcceptedTrace
open SwitchStack ControlSwitch

theorem rail_step (φ : Complexity.SAT.CNF) (v : Fin (varCount φ)) (b : Bool)
    (j : Fin (levels φ + 1)) (hj : j.val < levels φ) {y : External φ}
    (h : Step φ (.rail v b j) y) :
    ∃ k : Fin (levels φ + 1), y = .rail v b k ∧ k.val = j.val + 1 := by
  rcases h with h | ⟨i,a,c,hx,hm,hy⟩
  · cases y with
    | var w => simp [adjacency,Edge,DataWire] at h; omega
    | clause w => simp [adjacency,Edge,DataWire] at h
    | rail w d k =>
      simp [adjacency,Edge,DataWire] at h
      obtain ⟨hvw,hbd,hjk,_⟩ := h
      subst w; subst d
      exact ⟨k,rfl,hjk⟩
  · rcases hm with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simp [DataWire,sw] at hx
    · simp [DataWire,sw] at hx
      cases y with
      | var w => simp [DataWire,sw] at hy
      | clause w => simp [DataWire,sw] at hy
      | rail w d k =>
        simp [DataWire,sw] at hy
        obtain ⟨hvw,hbd⟩ := blocked_unique φ i hx.2 hy.2
        subst w; subst d
        exact ⟨k,rfl,by omega⟩

/-- Once a rail is entered, all its cursor positions occur with that Boolean
value. The endpoint is a clause vertex, so no rail position can be terminal. -/
theorem rail_fill (φ : Complexity.SAT.CNF) {trace : List (External φ)}
    {p : List (Vertex φ)} (hc : trace.IsChain (ObservedStep φ p))
    (he : trace.getLast? = some (finish φ))
    (v : Fin (varCount φ)) (b : Bool)
    (hzero : External.rail v b ⟨0,Nat.zero_lt_succ _⟩ ∈ trace) :
    ∀ j : Fin (levels φ + 1), External.rail v b j ∈ trace := by
  have hall : ∀ n, ∀ hn : n < levels φ + 1, External.rail v b ⟨n,hn⟩ ∈ trace := by
    intro n
    induction n with
    | zero => intro hn; exact hzero
    | succ n ih =>
      intro hn
      have hj : n < levels φ := by omega
      have hm := ih (by omega)
      obtain ⟨y,hs,hy⟩ := SwitchSegments.successor hc hm
        (by rw [he]; simp [finish])
      obtain ⟨k,rfl,hk⟩ := rail_step φ v b ⟨n,by omega⟩ hj (observed_step φ hs)
      have heq : k = ⟨n+1,hn⟩ := Fin.ext hk
      simpa [heq] using hy
  intro j
  exact hall j.val j.isLt

theorem rail_start_rank (φ : Complexity.SAT.CNF) (v : Fin (varCount φ))
    (x : External φ) (h : rank φ x = v.val * (levels φ + 2) + 1) :
    ∃ b, x = External.rail v b ⟨0,Nat.zero_lt_succ _⟩ := by
  cases x with
  | var w =>
    have hm := congrArg (fun z => z % (levels φ + 2)) h
    simp [rank,Nat.add_mod,Nat.mod_eq_of_lt (show 1 < levels φ + 2 by omega)] at hm
  | clause c =>
    have hm := Nat.mul_le_mul_right (levels φ + 2) v.isLt
    simp only [rank] at h
    nlinarith
  | rail w b j =>
    have hj := j.isLt
    simp only [rank] at h
    have hvw : v.val = w.val := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hm := Nat.mul_le_mul_right (levels φ + 2) (Nat.succ_le_of_lt hlt)
        simp only [Nat.succ_mul] at hm
        omega
      · have hm := Nat.mul_le_mul_right (levels φ + 2) (Nat.succ_le_of_lt hgt)
        simp only [Nat.succ_mul] at hm
        omega
    have hw : w = v := Fin.ext hvw.symm
    subst w
    have hj0 : j = ⟨0,Nat.zero_lt_succ _⟩ := Fin.ext (by change j.val = 0; omega)
    subst j
    exact ⟨b,rfl⟩

/-- Unit advancement forces every intermediate rank to occur. -/
theorem rank_coverage (φ : Complexity.SAT.CNF) (a : External φ)
    (tail : List (External φ)) {p : List (Vertex φ)} {t : External φ} {k : Nat}
    (hc : (a :: tail).IsChain (ObservedStep φ p))
    (he : (a :: tail).getLast? = some t)
    (ha : rank φ a ≤ k) (ht : k ≤ rank φ t) :
    ∃ v ∈ a :: tail, rank φ v = k := by
  induction tail generalizing a with
  | nil =>
    have hat : a = t := by simpa using he
    subst t
    exact ⟨a,by simp,by omega⟩
  | cons b tail ih =>
    by_cases hak : rank φ a = k
    · exact ⟨a,by simp,hak⟩
    · have hs := List.isChain_cons_cons.mp hc
      have hb := step_rank φ (observed_step φ hs.1)
      obtain ⟨v,hv,hvk⟩ := ih b hs.2 (by simpa using he) (by omega)
      exact ⟨v,List.mem_cons_of_mem _ hv,hvk⟩

/-- Coverage is derived from an actual accepted pair, not postulated for an
abstract graph path. The observed trace retains its original suffix. -/
theorem accepted_rank_coverage (φ : Complexity.SAT.CNF) {p q : List (Vertex φ)}
    (h : Accepted φ p q) :
    ∃ pre tail, ∃ trace : List (External φ),
      p = pre ++ [SwitchStack.sw (top φ) 5] ++ (Sum.inr (start φ) :: tail) ∧
      trace.head? = some (start φ) ∧ trace.getLast? = some (finish φ) ∧
      trace.IsChain (ObservedStep φ (Sum.inr (start φ) :: tail)) ∧
      (∀ i : Fin (levels φ), ¬(SwitchStack.sw i 2 ∈ Sum.inr (start φ) :: tail ∧
        SwitchStack.sw i 3 ∈ Sum.inr (start φ) :: tail)) ∧
      (∀ k ≤ varCount φ * (levels φ + 2) + φ.length + 1,
        ∃ v ∈ trace, rank φ v = k) := by
  obtain ⟨pre,tail,trace,heq,hh,hl,hc,hex⟩ := accepted_trace φ h
  refine ⟨pre,tail,trace,heq,hh,hl,hc,hex,?_⟩
  intro k hk
  cases trace with
  | nil => simp at hh
  | cons a rest =>
    have ha : a = start φ := by simpa using hh
    subst a
    exact rank_coverage φ (start φ) rest hc hl (by simp [rank,start])
      (by simpa [rank,finish] using hk)

/-- Every variable has a single chosen Boolean value whose entire rail occurs
in the actual observed trace. This is existence, not yet a SAT assignment. -/
theorem accepted_boolean_rails (φ : Complexity.SAT.CNF) {p q : List (Vertex φ)}
    (h : Accepted φ p q) :
    ∃ pre tail, ∃ (trace : List (External φ)) (σ : Fin (varCount φ) → Bool),
      p = pre ++ [sw (top φ) 5] ++ (Sum.inr (start φ) :: tail) ∧
      trace.head? = some (start φ) ∧ trace.getLast? = some (finish φ) ∧
      trace.IsChain (ObservedStep φ (Sum.inr (start φ) :: tail)) ∧
      (∀ i : Fin (levels φ), ¬(sw i 2 ∈ Sum.inr (start φ) :: tail ∧
        sw i 3 ∈ Sum.inr (start φ) :: tail)) ∧
      (∀ k ≤ varCount φ * (levels φ + 2) + φ.length + 1,
        ∃ x ∈ trace, rank φ x = k) ∧
      (∀ v j, External.rail v (σ v) j ∈ trace) := by
  classical
  obtain ⟨pre,tail,trace,heq,hh,hl,hc,hex,hcover⟩ := accepted_rank_coverage φ h
  have hall : ∀ v : Fin (varCount φ), ∃ b : Bool,
      ∀ j : Fin (levels φ + 1), External.rail v b j ∈ trace := by
    intro v
    have hbound := Nat.mul_le_mul_right (levels φ + 2) (Nat.le_of_lt v.isLt)
    obtain ⟨x,hx,hxr⟩ := hcover (v.val * (levels φ + 2) + 1) (by omega)
    obtain ⟨b,rfl⟩ := rail_start_rank φ v x hxr
    exact ⟨b,rail_fill φ hc hl v b hx⟩
  choose σ hσ using hall
  exact ⟨pre,tail,trace,σ,heq,hh,hl,hc,hex,hcover,hσ⟩

theorem rank_lt_tail (φ : Complexity.SAT.CNF) {p : List (Vertex φ)}
    (a : External φ) (tail : List (External φ))
    (hc : (a :: tail).IsChain (ObservedStep φ p)) :
    ∀ b ∈ tail, rank φ a < rank φ b := by
  induction tail generalizing a with
  | nil => simp
  | cons b tail ih =>
    have hs := List.isChain_cons_cons.mp hc
    have hab := step_rank φ (observed_step φ hs.1)
    intro c hm
    rcases List.mem_cons.mp hm with rfl | hm
    · omega
    · have hbc := ih b hs.2 c hm
      omega

theorem rank_injective_on_trace (φ : Complexity.SAT.CNF) {p : List (Vertex φ)}
    (trace : List (External φ)) (hc : trace.IsChain (ObservedStep φ p))
    {x y : External φ} (hx : x ∈ trace) (hy : y ∈ trace)
    (he : rank φ x = rank φ y) : x = y := by
  induction trace with
  | nil => simp at hx
  | cons a tail ih =>
    rcases List.mem_cons.mp hx with rfl | hxt
    · rcases List.mem_cons.mp hy with rfl | hyt
      · rfl
      · have hlt := rank_lt_tail φ x tail hc y hyt
        omega
    · rcases List.mem_cons.mp hy with rfl | hyt
      · have hlt := rank_lt_tail φ y tail hc x hxt
        omega
      · exact ih hc.tail hxt hyt

/-- No contrary rail value can occur at the same cursor in an observed trace. -/
theorem rail_value_unique (φ : Complexity.SAT.CNF) {p : List (Vertex φ)}
    {trace : List (External φ)} (hc : trace.IsChain (ObservedStep φ p))
    (v : Fin (varCount φ)) (j : Fin (levels φ + 1)) {b c : Bool}
    (hb : External.rail v b j ∈ trace) (hc' : External.rail v c j ∈ trace) : b = c := by
  have he := rank_injective_on_trace φ trace hc hb hc' rfl
  simpa using he

end UnconstrainedPACDetection.VariableAssignment

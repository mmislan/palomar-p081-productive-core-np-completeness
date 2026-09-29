module

public import proofs.UnconstrainedPACDetection.LogicalTrace

@[expose] public section

namespace UnconstrainedPACDetection.ExternalTrace
open FormulaWiring LogicalTrace SwitchStack ControlSwitch

theorem data_exit_external (φ : Complexity.SAT.CNF) (i : Fin (levels φ))
    {b : V} {x : Vertex φ} (hb : b = 6 ∨ b = 7)
    (hx : adjacency φ (sw i b) x) :
    ∃ y : External φ, x = Sum.inr y ∧ DataWire φ (sw i b) (Sum.inr y) := by
  cases x with
  | inl z =>
    obtain ⟨j,a⟩ := z
    rcases hb with rfl | rfl <;> simp [adjacency,Edge,sw,DataWire,next,edges] at hx
  | inr y =>
    refine ⟨y,rfl,?_⟩
    exact hx.2

/-- Every actual residual visit returns immediately to an external vertex in
the concrete formula graph, retaining the exact contiguous remainder. -/
theorem visit_external (φ : Complexity.SAT.CNF) (i : Fin (levels φ))
    {a : V} {tail : List (Vertex φ)} {t : External φ} {up down : List V}
    (hc : (sw i a :: tail).IsChain (adjacency φ))
    (hn : (sw i a :: tail).Nodup)
    (he : (sw i a :: tail).getLast? = some (Sum.inr t))
    (hu : Path 0 4 up) (hd : Path 1 5 down) (hud : up.Disjoint down)
    (havoid : ∀ v ∈ up ++ down, sw i v ∉ sw i a :: tail)
    (ha : input a) :
    ∃ b segment, ∃ (y : External φ) (rest : List (Vertex φ)), Path a b segment ∧
      segment.map (sw i) ++ (Sum.inr y :: rest) = sw i a :: tail ∧
      ((a = 2 ∧ b = 6) ∨ (a = 3 ∧ b = 7)) ∧
      DataWire φ (sw i b) (Sum.inr y) := by
  obtain ⟨b,segment,rest,hp,heq,hm⟩ := visit_prefix φ i hc hn he hu hd hud havoid ha
  have hl : (segment.map (sw (X := External φ) i)).getLast? = some (sw i b) := by
    simp [hp.2.1]
  have hc' : (segment.map (sw i) ++ rest).IsChain (adjacency φ) := heq.symm ▸ hc
  cases rest with
  | nil =>
    rw [← heq] at he
    simp only [List.append_nil,hl] at he
    simp [sw] at he
  | cons x xs =>
    have hx : adjacency φ (sw i b) x :=
      (List.isChain_append.mp hc').2.2 _ (by rw [hl]; rfl) _ (by rfl)
    have hb : b = 6 ∨ b = 7 := hm.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
    obtain ⟨y,rfl,hy⟩ := data_exit_external φ i hb hx
    exact ⟨b,segment,y,xs,hp,heq,hm,hy⟩

/-- A trace edge retains evidence that its occurrence input was actually used.
This information is needed later to apply suffix exclusivity. -/
def ObservedStep (φ : Complexity.SAT.CNF) (ambient : List (Vertex φ))
    (x y : External φ) : Prop :=
  adjacency φ (Sum.inr x) (Sum.inr y) ∨
  ∃ i a b, DataWire φ (Sum.inr x) (sw i a) ∧
    ((a = 2 ∧ b = 6) ∨ (a = 3 ∧ b = 7)) ∧
    DataWire φ (sw i b) (Sum.inr y) ∧ sw i a ∈ ambient

theorem observed_step (φ : Complexity.SAT.CNF) {p : List (Vertex φ)}
    {x y : External φ} (h : ObservedStep φ p x y) : Step φ x y := by
  rcases h with h | ⟨i,a,b,hx,hm,hy,_⟩
  · exact Or.inl h
  · exact Or.inr ⟨i,a,b,hx,hm,hy⟩

/-- Find the next external vertex along the actual path, with a strictly
shorter remainder and the observed occurrence retained. -/
theorem next_external (φ : Complexity.SAT.CNF) (x : External φ) (z : Vertex φ)
    (tail : List (Vertex φ)) {t : External φ}
    (hc : (Sum.inr x :: z :: tail).IsChain (adjacency φ))
    (hn : (Sum.inr x :: z :: tail).Nodup)
    (he : (Sum.inr x :: z :: tail).getLast? = some (Sum.inr t))
    (hcontrols : ∀ i : Fin (levels φ), ∃ up down,
      Path 0 4 up ∧ Path 1 5 down ∧ up.Disjoint down ∧
      ∀ v ∈ up ++ down, sw i v ∉ Sum.inr x :: z :: tail) :
    ∃ (y : External φ) (middle rest : List (Vertex φ)),
      middle ++ (Sum.inr y :: rest) = z :: tail ∧
      ObservedStep φ (Sum.inr x :: z :: tail) x y ∧ rest.length < (z :: tail).length := by
  have hx := (List.isChain_cons_cons.mp hc).1
  cases z with
  | inr y => exact ⟨y,[],tail,rfl,Or.inl hx,by simp⟩
  | inl z =>
    obtain ⟨i,a⟩ := z
    have hin : (a = 2 ∨ a = 3) ∧ DataWire φ (Sum.inr x) (sw i a) := hx
    have ha : input a := by rcases hin.1 with rfl | rfl <;> simp [input]
    obtain ⟨up,down,hu,hd,hud,havoid⟩ := hcontrols i
    obtain ⟨b,segment,y,rest,hp,heq,hm,hy⟩ := visit_external φ i hc.tail hn.tail
      (by simpa only [List.getLast?_cons_cons, sw] using he) hu hd hud
      (by intro v hv hs; exact havoid v hv (List.mem_cons_of_mem _ hs)) ha
    refine ⟨y,segment.map (sw i),rest,heq,Or.inr ⟨i,a,b,hin.2,hm,hy,by simp [sw]⟩,?_⟩
    have hlen := congrArg List.length heq
    simp only [List.length_append,List.length_map,List.length_cons] at hlen ⊢
    omega

theorem observed_mono (φ : Complexity.SAT.CNF) {p q : List (Vertex φ)}
    (hsub : ∀ v ∈ p, v ∈ q) {x y : External φ}
    (h : ObservedStep φ p x y) : ObservedStep φ q x y := by
  rcases h with h | ⟨i,a,b,hx,hm,hy,hin⟩
  · exact Or.inl h
  · exact Or.inr ⟨i,a,b,hx,hm,hy,hsub _ hin⟩

theorem trace_bounded (φ : Complexity.SAT.CNF) (N : Nat) :
    ∀ (x : External φ) (tail : List (Vertex φ)) (t : External φ), tail.length < N →
    (Sum.inr x :: tail).IsChain (adjacency φ) → (Sum.inr x :: tail).Nodup →
    (Sum.inr x :: tail).getLast? = some (Sum.inr t) →
    (∀ i : Fin (levels φ), ∃ up down,
      Path 0 4 up ∧ Path 1 5 down ∧ up.Disjoint down ∧
      ∀ v ∈ up ++ down, sw i v ∉ Sum.inr x :: tail) →
    ∃ trace : List (External φ), trace.head? = some x ∧ trace.getLast? = some t ∧
      trace.IsChain (ObservedStep φ (Sum.inr x :: tail)) := by
  induction N with
  | zero => intro x tail t hlen; omega
  | succ N ih =>
    intro x tail t hlen hc hn he hcontrols
    cases tail with
    | nil =>
      have hxt : x = t := by simpa using he
      subst t
      exact ⟨[x],rfl,rfl,.singleton _⟩
    | cons z tail =>
      obtain ⟨y,middle,rest,heq,hs,hr⟩ := next_external φ x z tail hc hn he hcontrols
      have hsub : ∀ v ∈ Sum.inr y :: rest, v ∈ Sum.inr x :: z :: tail := by
        intro v hv
        apply List.mem_cons_of_mem
        rw [← heq]
        exact List.mem_append_right _ hv
      have hcr : (Sum.inr y :: rest).IsChain (adjacency φ) := by
        have h : (middle ++ (Sum.inr y :: rest)).IsChain (adjacency φ) := heq.symm ▸ hc.tail
        exact (List.isChain_append.mp h).2.1
      have hnr : (Sum.inr y :: rest).Nodup := by
        have h : (middle ++ (Sum.inr y :: rest)).Nodup := heq.symm ▸ hn.tail
        exact h.of_append_right
      have her : (Sum.inr y :: rest).getLast? = some (Sum.inr t) := by
        have h : (z :: tail).getLast? = some (Sum.inr t) := by simpa using he
        rw [← heq] at h
        simpa using h
      have hcon : ∀ i : Fin (levels φ), ∃ up down,
          Path 0 4 up ∧ Path 1 5 down ∧ up.Disjoint down ∧
          ∀ v ∈ up ++ down, sw i v ∉ Sum.inr y :: rest := by
        intro i
        obtain ⟨up,down,hu,hd,hud,hav⟩ := hcontrols i
        exact ⟨up,down,hu,hd,hud,fun v hv hm => hav v hv (hsub _ hm)⟩
      obtain ⟨trace,hh,hl,hchain⟩ := ih y rest t (by omega) hcr hnr her hcon
      have hchain' : trace.IsChain (ObservedStep φ (Sum.inr x :: z :: tail)) :=
        hchain.imp (fun _ _ h => observed_mono φ hsub h)
      cases trace with
      | nil => simp at hh
      | cons y' ys =>
        have hyy : y' = y := by simpa using hh
        subst y'
        exact ⟨x :: y :: ys,rfl,by simpa using hl,List.isChain_cons_cons.mpr ⟨hs,hchain'⟩⟩

/-- An entire actual residual path has an external trace, with every switch
step tied to an input occurring in that same original path. -/
theorem trace_exists (φ : Complexity.SAT.CNF) (x : External φ)
    (tail : List (Vertex φ)) (t : External φ)
    (hc : (Sum.inr x :: tail).IsChain (adjacency φ)) (hn : (Sum.inr x :: tail).Nodup)
    (he : (Sum.inr x :: tail).getLast? = some (Sum.inr t))
    (hcontrols : ∀ i : Fin (levels φ), ∃ up down,
      Path 0 4 up ∧ Path 1 5 down ∧ up.Disjoint down ∧
      ∀ v ∈ up ++ down, sw i v ∉ Sum.inr x :: tail) :
    ∃ trace : List (External φ), trace.head? = some x ∧ trace.getLast? = some t ∧
      trace.IsChain (ObservedStep φ (Sum.inr x :: tail)) :=
  trace_bounded φ (tail.length+1) x tail t (by omega) hc hn he hcontrols

end UnconstrainedPACDetection.ExternalTrace

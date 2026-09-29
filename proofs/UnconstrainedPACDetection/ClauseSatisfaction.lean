module

public import proofs.UnconstrainedPACDetection.VariableAssignment

@[expose] public section

namespace UnconstrainedPACDetection.ClauseSatisfaction
open FormulaWiring LogicalTrace ExternalTrace AcceptedTrace VariableAssignment SwitchStack ControlSwitch

theorem clause_rank (φ : Complexity.SAT.CNF) (c : Fin (φ.length + 1))
    (x : External φ) (h : rank φ x = varCount φ * (levels φ + 2) + c.val + 1) :
    x = External.clause c := by
  cases x with
  | var v =>
    have hm := Nat.mul_le_mul_right (levels φ + 2) (Nat.le_of_lt_succ v.isLt)
    simp only [rank] at h
    omega
  | rail v b j =>
    have hm := Nat.mul_le_mul_right (levels φ + 2) v.isLt
    simp only [Nat.succ_mul] at hm
    have hj := j.isLt
    simp only [rank] at h
    omega
  | clause d =>
    have hd : d = c := Fin.ext (by simp only [rank] at h; omega)
    subst d
    rfl

theorem clause_step_input (φ : Complexity.SAT.CNF) (c : Fin (φ.length + 1))
    {p : List (Vertex φ)} {y : External φ}
    (h : ObservedStep φ p (.clause c) y) :
    ∃ i l, lookup φ i = some (c.val,l) ∧ sw i 2 ∈ p := by
  rcases h with h | ⟨i,a,b,hx,_,_,hin⟩
  · cases y <;> simp [adjacency,Edge,DataWire] at h
  · simp [DataWire,sw] at hx
    obtain ⟨rfl,l,hl⟩ := hx
    exact ⟨i,l,hl,hin⟩

theorem blocked_step_input (φ : Complexity.SAT.CNF) (i : Fin (levels φ))
    (v : Fin (varCount φ)) (b : Bool) {p : List (Vertex φ)} {y : External φ}
    (hb : blocked φ i v b = true)
    (h : ObservedStep φ p (.rail v b ⟨i.val,by have := i.isLt; omega⟩) y) :
    sw i 3 ∈ p := by
  rcases h with h | ⟨j,a,c,hx,_,_,hin⟩
  · cases y with
    | var w => simp [adjacency,Edge,DataWire] at h; have := i.isLt; omega
    | clause w => simp [adjacency,Edge,DataWire] at h
    | rail w d k =>
      simp [adjacency,Edge,DataWire] at h
      obtain ⟨rfl,rfl,_,hbad⟩ := h
      simp_all
  · simp [DataWire,sw] at hx
    obtain ⟨rfl,hij,_⟩ := hx
    have hij' : i = j := Fin.ext hij
    subst j
    exact hin

theorem blocked_input_present (φ : Complexity.SAT.CNF)
    {trace : List (External φ)} {p : List (Vertex φ)}
    (hc : trace.IsChain (ObservedStep φ p)) (he : trace.getLast? = some (finish φ))
    (i : Fin (levels φ)) (v : Fin (varCount φ)) (b : Bool)
    (hm : External.rail v b ⟨i.val,by have := i.isLt; omega⟩ ∈ trace)
    (hb : blocked φ i v b = true) : sw i 3 ∈ p := by
  obtain ⟨y,hs,_⟩ := SwitchSegments.successor hc hm (by rw [he]; simp [finish])
  exact blocked_step_input φ i v b hb hs

theorem lookup_clause (φ : Complexity.SAT.CNF) (i : Fin (levels φ))
    {c : Nat} {l : Complexity.SAT.Lit} (h : lookup φ i = some (c,l)) :
    ∃ cl, φ[c]? = some cl ∧ l ∈ cl := by
  have hm : (c,l) ∈ occurrences φ := List.mem_of_getElem? h
  simp only [occurrences,List.mem_flatMap,List.mem_map] at hm
  obtain ⟨⟨cl,j⟩,hcl,l',hl,he⟩ := hm
  have he' : j = c ∧ l' = l := Prod.mk.inj he
  rcases he' with ⟨rfl,rfl⟩
  exact ⟨cl,List.mk_mem_zipIdx_iff_getElem?.mp hcl,hl⟩

/-- Every clause has a literal true under the one finite Boolean function
extracted from the actual accepted pair. -/
theorem accepted_clause_truth (φ : Complexity.SAT.CNF) {p q : List (Vertex φ)}
    (h : Accepted φ p q) :
    ∃ σ : Fin (varCount φ) → Bool, ∀ c : Fin φ.length,
      ∃ l ∈ φ[c.val], ∃ hv : l.var < varCount φ, σ ⟨l.var,hv⟩ = l.sign := by
  obtain ⟨pre,tail,trace,σ,_,_,hl,hc,hex,hcover,hrails⟩ := accepted_boolean_rails φ h
  refine ⟨σ,?_⟩
  intro c
  let ci : Fin (φ.length+1) := ⟨c.val,by have := c.isLt; omega⟩
  obtain ⟨x,hx,hxr⟩ := hcover (varCount φ * (levels φ + 2) + ci.val + 1)
    (by dsimp [ci]; have := c.isLt; omega)
  have hxc := clause_rank φ ci x hxr
  subst x
  obtain ⟨y,hs,_⟩ := SwitchSegments.successor hc hx (by
    rw [hl]
    simp [finish,ci,Fin.ext_iff]
    have := c.isLt
    omega)
  obtain ⟨i,l,hlook,hleft⟩ := clause_step_input φ ci hs
  obtain ⟨cl,hcl,hlit⟩ := lookup_clause φ i hlook
  have hcl' : cl = φ[c.val] := by
    have hget := List.getElem?_eq_getElem c.isLt
    exact Option.some.inj (hcl.symm.trans hget)
  subst cl
  have hv : l.var < varCount φ := by
    have h1 := Complexity.SAT.Clause.var_le_maxVar hlit
    have h2 := Complexity.SAT.CNF.clause_maxVar_le_maxVar (List.getElem_mem c.isLt)
    dsimp [varCount]
    omega
  refine ⟨l,hlit,hv,?_⟩
  by_contra hfalse
  have hb : blocked φ i ⟨l.var,hv⟩ (σ ⟨l.var,hv⟩) = true :=
    (blocked_lookup φ i ⟨l.var,hv⟩ (σ ⟨l.var,hv⟩)).mpr
      ⟨ci.val,l,hlook,rfl,Ne.symm hfalse⟩
  have hright := blocked_input_present φ hc hl i ⟨l.var,hv⟩ (σ ⟨l.var,hv⟩)
    (hrails _ _) hb
  exact hex i ⟨hleft,hright⟩

end UnconstrainedPACDetection.ClauseSatisfaction

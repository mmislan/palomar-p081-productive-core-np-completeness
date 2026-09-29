module

public import proofs.UnconstrainedPACDetection.FormulaClauseDegree

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSwitchDegree
open Complexity.SAT FormulaWiring SwitchStack ControlSwitch FormulaOutdegree

def internalDegree (a : V) : Nat := Fintype.card {b : V // b ∈ next a}

theorem internal_total : (∑ a : V, internalDegree a) = 29 := by decide

private theorem degree_one (φ : CNF) (x z : Vertex φ)
    (h : ∀ y, adjacency φ x y ↔ y = z) : degree φ x = 1 := by
  unfold degree
  have he := Fintype.card_congr (Equiv.subtypeEquivRight h)
  simpa using he

private theorem degree_zero (φ : CNF) (x : Vertex φ)
    (h : ∀ y, ¬adjacency φ x y) : degree φ x = 0 := by
  unfold degree
  exact Fintype.card_eq_zero_iff.mpr ⟨fun y => h y.val y.property⟩

theorem ordinary_degree (φ : CNF) (i : Fin (levels φ)) (a : V)
    (h4 : a ≠ 4) (h5 : a ≠ 5) (h6 : a ≠ 6) (h7 : a ≠ 7) :
    degree φ (sw i a) = internalDegree a := by
  let f : {b : V // b ∈ next a} → {y : Vertex φ // adjacency φ (sw i a) y} :=
    fun b => ⟨sw i b.val,by simp [adjacency,Edge,sw,b.property]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro b c h
      have he := congrArg Subtype.val h
      change sw i b.val = sw i c.val at he
      simp only [sw,Sum.inl.injEq,Prod.mk.injEq,true_and] at he
      exact Subtype.ext he
    · rintro ⟨y,hy⟩
      cases y with
      | inl y =>
        obtain ⟨j,b⟩ := y
        simp [adjacency,Edge,sw,h4,h5,h6,h7] at hy
        obtain ⟨rfl,hb⟩ := hy
        exact ⟨⟨b,hb⟩,rfl⟩
      | inr y => simp [adjacency,Edge,sw,h5,h6,h7] at hy
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm

def port5Next (φ : CNF) (i : Fin (levels φ)) : Vertex φ :=
  if h : i.val+1 < levels φ then sw ⟨i.val+1,h⟩ 1 else .inr (.var 0)

theorem port5_iff (φ : CNF) (i : Fin (levels φ)) (y : Vertex φ) :
    adjacency φ (sw i 5) y ↔ y = port5Next φ i := by
  by_cases hi : i.val+1 < levels φ
  · have hn : i.val+1 ≠ levels φ := by omega
    cases y with
    | inl y =>
      obtain ⟨j,b⟩ := y
      simp [adjacency,Edge,sw,next,edges,DataWire,port5Next,hi]
      constructor
      · rintro ⟨hb,hj⟩; exact ⟨Fin.ext hj,hb⟩
      · rintro ⟨hj,hb⟩; exact ⟨hb,congrArg Fin.val hj⟩
    | inr y => cases y <;> simp [adjacency,Edge,sw,DataWire,port5Next,hi,hn]
  · have he : i.val+1 = levels φ := by have := i.isLt; omega
    cases y with
    | inl y =>
      obtain ⟨j,b⟩ := y
      have hj := j.isLt
      simp [adjacency,Edge,sw,next,edges,DataWire,port5Next,hi]
      omega
    | inr y => cases y <;> simp [adjacency,Edge,sw,DataWire,port5Next,he]

theorem port5_degree (φ : CNF) (i : Fin (levels φ)) : degree φ (sw i 5) = 1 :=
  degree_one φ _ _ (port5_iff φ i)

theorem port4_iff (φ : CNF) (i : Fin (levels φ)) (hi : 0 < i.val) (y : Vertex φ) :
    adjacency φ (sw i 4) y ↔ y = sw ⟨i.val-1,by have := i.isLt; omega⟩ 0 := by
  cases y with
  | inl y =>
    obtain ⟨j,b⟩ := y
    simp [adjacency,Edge,sw,next,edges,DataWire]
    constructor
    · rintro ⟨hb,hj⟩
      exact ⟨Fin.ext (show j.val = i.val-1 by omega),hb⟩
    · rintro ⟨hj,hb⟩
      have hv := congrArg Fin.val hj
      change j.val = i.val-1 at hv
      exact ⟨hb,by omega⟩
  | inr y => simp [adjacency,Edge,sw]

theorem port4_degree (φ : CNF) (i : Fin (levels φ)) :
    degree φ (sw i 4) = if 0 < i.val then 1 else 0 := by
  by_cases hi : 0 < i.val
  · rw [ite_eq_left hi]
    exact degree_one φ _ _ (port4_iff φ i hi)
  · rw [ite_eq_right hi]
    have he : i = ⟨0,levels_pos φ⟩ := Fin.ext (show i.val = 0 by omega)
    subst i
    exact degree_zero φ _ (FormulaNormalization.no_from_sinkQ φ)

private theorem lookup_clause_bound (φ : CNF) (i : Fin (levels φ)) {c : Nat} {l : Lit}
    (h : lookup φ i = some (c,l)) : c < φ.length := by
  obtain ⟨cl,hcl,_⟩ := ClauseSatisfaction.lookup_clause φ i h
  exact (List.getElem?_eq_some_iff.mp hcl).1

theorem port6_some_degree (φ : CNF) (i : Fin (levels φ)) {c : Nat} {l : Lit}
    (h : lookup φ i = some (c,l)) : degree φ (sw i 6) = 1 := by
  let target : Vertex φ := .inr (.clause ⟨c+1,Nat.succ_lt_succ (lookup_clause_bound φ i h)⟩)
  apply degree_one φ _ target
  intro y
  cases y with
  | inl y =>
    obtain ⟨j,a⟩ := y
    simp [adjacency,Edge,sw,next,edges,DataWire,target]
  | inr y =>
    cases y with
    | var v => simp [adjacency,Edge,sw,DataWire,target]
    | rail v b j => simp [adjacency,Edge,sw,DataWire,target]
    | clause d =>
      simp [adjacency,Edge,sw,DataWire,target,h]
      exact ⟨fun hd => Fin.ext hd,fun hd => congrArg Fin.val hd⟩

theorem port7_some_degree (φ : CNF) (i : Fin (levels φ)) {c : Nat} {l : Lit}
    (h : lookup φ i = some (c,l)) : degree φ (sw i 7) = 1 := by
  let v : Fin (varCount φ) := ⟨l.var,FormulaBlockingCardinality.literal_bound φ i h⟩
  let j : Fin (levels φ+1) := ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩
  have hb : blocked φ i v (!l.sign) = true := by simp [blocked,h,v]
  apply degree_one φ _ (.inr (.rail v (!l.sign) j))
  intro y
  cases y with
  | inl y =>
    obtain ⟨k,a⟩ := y
    simp [adjacency,Edge,sw,next,edges,DataWire]
  | inr y =>
    cases y with
    | var w => simp [adjacency,Edge,sw,DataWire]
    | clause d => simp [adjacency,Edge,sw,DataWire]
    | rail w b k =>
      simp [adjacency,Edge,sw,DataWire]
      constructor
      · rintro ⟨hk,hw⟩
        obtain ⟨hv,hb'⟩ := LogicalTrace.blocked_unique φ i hw hb
        exact ⟨hv,hb',Fin.ext hk⟩
      · rintro ⟨rfl,rfl,rfl⟩
        exact ⟨rfl,hb⟩

theorem data_none_degree (φ : CNF) (i : Fin (levels φ))
    (h : lookup φ i = none) (a : V) (ha : a = 6 ∨ a = 7) : degree φ (sw i a) = 0 := by
  apply degree_zero φ _
  intro y
  rcases ha with rfl | rfl
  · cases y with
    | inl y => obtain ⟨j,b⟩ := y; simp [adjacency,Edge,sw,next,edges,DataWire]
    | inr y => cases y <;> simp [adjacency,Edge,sw,DataWire,blocked,h]
  · cases y with
    | inl y => obtain ⟨j,b⟩ := y; simp [adjacency,Edge,sw,next,edges,DataWire]
    | inr y => cases y <;> simp [adjacency,Edge,sw,DataWire,blocked,h]

theorem port6_degree (φ : CNF) (i : Fin (levels φ)) :
    degree φ (sw i 6) = if (lookup φ i).isSome then 1 else 0 := by
  cases h : lookup φ i with
  | none => simpa using data_none_degree φ i h 6 (Or.inl rfl)
  | some o => obtain ⟨c,l⟩ := o; simpa using port6_some_degree φ i h

theorem port7_degree (φ : CNF) (i : Fin (levels φ)) :
    degree φ (sw i 7) = if (lookup φ i).isSome then 1 else 0 := by
  cases h : lookup φ i with
  | none => simpa using data_none_degree φ i h 7 (Or.inr rfl)
  | some o => obtain ⟨c,l⟩ := o; simpa using port7_some_degree φ i h

end UnconstrainedPACDetection.FormulaSwitchDegree

module

public import proofs.IrrRAFEnumeration.PositiveSupportedTrace
public import proofs.Complexitylib.SAT.Semantics

@[expose] public section

namespace IrrRAFEnumeration.PositiveCompletionCNF
open RAF Complexity.SAT

def positive (vs : List Nat) : Clause := vs.map (fun v => ⟨true,v⟩)
def negative (vs : List Nat) : Clause := vs.map (fun v => ⟨false,v⟩)
def implies (v : Nat) (vs : List Nat) : Clause := ⟨false,v⟩ :: positive vs
def each (n : Nat) (f : Fin n → CNF) : CNF := (List.finRange n).flatMap f
def selectVar {r : Nat} (j : Fin r) := j.val
def rowVar (r : Nat) {d : Nat} (i : Fin (d+1)) (x : Fin d) := r+i.val*d+x.val
def fireVar (d : Nat) {r : Nat} (i : Fin d) (j : Fin r) := r+(d+1)*d+i.val*r+j.val
def members {n : Nat} (P : Fin n → Prop) [DecidablePred P] (f : Fin n → Nat) :=
  ((List.finRange n).filter (fun x => decide (P x))).map f

/-- Literal-level translation of the supported certificate. The arithmetic
indices match the execution preflight. Empty clauses are retained. -/
def formula {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) : CNF :=
  [positive ((List.finRange r).map selectVar)] ++
  each r (fun j => if j ∈ U then [] else [negative [selectVar j]]) ++
  each d (fun x => if x ∈ Q.food then [] else [negative [rowVar r ⟨0,by omega⟩ x]]) ++
  each d (fun i => each r (fun j =>
    [implies (fireVar d i j) [selectVar j]] ++
    each d (fun x => if x ∈ Q.inputs j then
      [implies (fireVar d i j) [rowVar r ⟨i.val,by omega⟩ x]] else []))) ++
  each d (fun i => each d (fun x =>
    [implies (rowVar r ⟨i.val+1,by omega⟩ x)
      (rowVar r ⟨i.val,by omega⟩ x :: members (fun j => x ∈ Q.outputs j) (fireVar d i))])) ++
  each r (fun j =>
    each d (fun x => if x ∈ Q.inputs j then
      [implies (selectVar j) [rowVar r ⟨d,by omega⟩ x]] else []) ++
    [implies (selectVar j) (members (fun x => C x j) (rowVar r ⟨d,by omega⟩))]) ++
  G.map (fun I => negative (members (fun j => j ∈ I) selectVar))

@[simp] theorem eval_positive (a : Assignment) (vs : List Nat) :
    Clause.eval a (positive vs) = true ↔ ∃ v ∈ vs, a.get v = true := by
  simp [Clause.eval,positive,Lit.eval,List.any_eq_true]

@[simp] theorem eval_negative (a : Assignment) (vs : List Nat) :
    Clause.eval a (negative vs) = true ↔ ∃ v ∈ vs, a.get v = false := by
  simp [Clause.eval,negative,Lit.eval,List.any_eq_true]

@[simp] theorem eval_implies (a : Assignment) (v : Nat) (vs : List Nat) :
    Clause.eval a (implies v vs) = true ↔ (a.get v = true → ∃ w ∈ vs, a.get w = true) := by
  cases h : a.get v <;> simp [implies,Clause.eval,Lit.eval,h,positive,List.any_eq_true]

@[simp] theorem eval_each (a : Assignment) (n : Nat) (f : Fin n → CNF) :
    CNF.eval a (each n f) = true ↔ ∀ i, CNF.eval a (f i) = true := by
  simp [CNF.eval,each,List.all_eq_true]

@[simp] theorem mem_members {n : Nat} (P : Fin n → Prop) [DecidablePred P]
    (f : Fin n → Nat) (v : Nat) : v ∈ members P f ↔ ∃ x, P x ∧ f x = v := by
  simp [members]

@[simp] theorem eval_append (a : Assignment) (p q : CNF) :
    CNF.eval a (p++q) = true ↔ CNF.eval a p = true ∧ CNF.eval a q = true := by
  simp [CNF.eval]

@[simp] theorem eval_singleton (a : Assignment) (c : Clause) :
    CNF.eval a [c] = true ↔ Clause.eval a c = true := by
  simp [CNF.eval]

@[simp] theorem eval_guard (a : Assignment) {n : Nat} (P : Fin n → Prop)
    [DecidablePred P] (f : Fin n → Clause) :
    CNF.eval a (each n (fun i => if P i then [f i] else [])) = true ↔
      ∀ i, P i → Clause.eval a (f i) = true := by
  rw [eval_each]
  apply forall_congr'
  intro i
  by_cases h : P i <;> simp [h]

@[simp] theorem eval_exclude (a : Assignment) {n : Nat} (P : Fin n → Prop)
    [DecidablePred P] (f : Fin n → Clause) :
    CNF.eval a (each n (fun i => if P i then [] else [f i])) = true ↔
      ∀ i, ¬ P i → Clause.eval a (f i) = true := by
  rw [eval_each]
  apply forall_congr'
  intro i
  by_cases h : P i <;> simp [h]

def BitsCheck {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) (G : List (Finset (Fin r)))
    (U : Finset (Fin r)) (a : Assignment) : Prop :=
  (∃ j : Fin r, a.get (selectVar j) = true) ∧
  (∀ j, j ∉ U → a.get (selectVar j) = false) ∧
  (∀ x, x ∉ Q.food → a.get (rowVar r ⟨0,by omega⟩ x) = false) ∧
  (∀ i : Fin d, ∀ j : Fin r,
    (a.get (fireVar d i j) = true → a.get (selectVar j) = true) ∧
    (∀ x ∈ Q.inputs j, a.get (fireVar d i j) = true →
      a.get (rowVar r ⟨i.val,by omega⟩ x) = true)) ∧
  (∀ i : Fin d, ∀ x : Fin d, a.get (rowVar r ⟨i.val+1,by omega⟩ x) = true →
    a.get (rowVar r ⟨i.val,by omega⟩ x) = true ∨
      ∃ j, x ∈ Q.outputs j ∧ a.get (fireVar d i j) = true) ∧
  (∀ j : Fin r,
    (∀ x ∈ Q.inputs j, a.get (selectVar j) = true →
      a.get (rowVar r ⟨d,by omega⟩ x) = true) ∧
    (a.get (selectVar j) = true → ∃ x, C x j ∧ a.get (rowVar r ⟨d,by omega⟩ x) = true)) ∧
  (∀ I ∈ G, ∃ j ∈ I, a.get (selectVar j) = false)

@[simp] theorem eval_map {α : Type*} (a : Assignment) (xs : List α) (f : α → Clause) :
    CNF.eval a (xs.map f) = true ↔ ∀ x ∈ xs, Clause.eval a (f x) = true := by
  simp [CNF.eval,List.all_eq_true]

@[simp] theorem eval_if_clause (a : Assignment) (P : Prop) [Decidable P] (c : Clause) :
    CNF.eval a (if P then [c] else []) = true ↔ (P → Clause.eval a c = true) := by
  by_cases h : P <;> simp [h]

@[simp] theorem eval_unless_clause (a : Assignment) (P : Prop) [Decidable P] (c : Clause) :
    CNF.eval a (if P then [] else [c]) = true ↔ (¬ P → Clause.eval a c = true) := by
  by_cases h : P <;> simp [h]

theorem formula_eval_iff {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r)) (a : Assignment) :
    CNF.eval a (formula Q C G U) = true ↔ BitsCheck Q C G U a := by
  simp [formula,BitsCheck]

theorem bitsCheck_sound {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) (G : List (Finset (Fin r)))
    (U : Finset (Fin r)) (a : Assignment) (h : BitsCheck Q C G U a) :
    PositiveCompletion.Available (IsRAF Q C) G.toFinset U := by
  obtain ⟨hne,hU,hfood,hfire,hstep,hend,hG⟩ := h
  let S : Finset (Fin r) := Finset.univ.filter (fun j => a.get (selectVar j) = true)
  have hS (j : Fin r) : j ∈ S ↔ a.get (selectVar j) = true := by simp [S]
  have hgen : ∀ k, k ≤ d → ∀ x : Fin d,
      a.get (r+k*d+x.val) = true → x ∈ closureAt Q S k := by
    intro k
    induction k with
    | zero =>
      intro _ x hx
      change x ∈ Q.food
      by_contra hn
      have hz := hfood x hn
      change a.get (r+0*d+x.val) = false at hz
      exact Bool.noConfusion (hx.symm.trans hz)
    | succ k ih =>
      intro hk x hx
      have hk' : k < d := by omega
      have hp := ih (by omega)
      have hv := hstep ⟨k,hk'⟩ x hx
      rcases hv with hv | ⟨j,hout,hf⟩
      · exact Finset.mem_union_left _ (hp x hv)
      · have hj : j ∈ S := (hS j).mpr ((hfire ⟨k,hk'⟩ j).1 hf)
        have he : Enabled Q (closureAt Q S k) j := by
          intro y hy
          exact hp y ((hfire ⟨k,hk'⟩ j).2 y hy hf)
        simp only [closureAt,closureStep,Finset.mem_union,Finset.mem_biUnion]
        exact Or.inr ⟨j,hj,by simpa only [ite_eq_left he] using hout⟩
  refine ⟨S,?_,?_,?_⟩
  · intro j hj
    by_contra hn
    exact Bool.noConfusion (((hS j).mp hj).symm.trans (hU j hn))
  · refine ⟨?_,?_,?_⟩
    · obtain ⟨j,hj⟩ := hne
      exact ⟨j,(hS j).mpr hj⟩
    · intro j hj
      refine ⟨d,?_⟩
      intro x hx
      exact hgen d (by omega) x ((hend j).1 x hx ((hS j).mp hj))
    · intro j hj
      obtain ⟨x,hc,hx⟩ := (hend j).2 ((hS j).mp hj)
      exact ⟨x,d,hgen d (by omega) x hx,hc⟩
  · intro I hI hIS
    obtain ⟨j,hj,hfalse⟩ := hG I (List.mem_toFinset.mp hI)
    exact Bool.noConfusion (((hS j).mp (hIS hj)).symm.trans hfalse)

theorem formula_sound {d r : Nat} (Q : CRS (Fin d) (Fin r))
    (C : Catalysis (Fin d) (Fin r)) [DecidableRel C]
    (G : List (Finset (Fin r))) (U : Finset (Fin r))
    (h : (formula Q C G U).Satisfiable) :
    PositiveCompletion.Available (IsRAF Q C) G.toFinset U := by
  obtain ⟨a,ha⟩ := h
  exact bitsCheck_sound Q C G U a ((formula_eval_iff Q C G U a).mp ha)

end IrrRAFEnumeration.PositiveCompletionCNF

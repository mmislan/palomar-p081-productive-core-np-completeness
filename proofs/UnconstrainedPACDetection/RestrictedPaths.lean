module

public import Mathlib.Tactic

@[expose] public section

namespace UnconstrainedPACDetection.RestrictedPaths

def Edge {X : Type*} (A : X → X → Prop) (S : X → Prop) (x y : X) : Prop :=
  A x y ∧ S x ∧ S y

abbrev Reach {X : Type*} (A : X → X → Prop) (S : X → Prop) :=
  Relation.ReflTransGen (Edge A S)

theorem of_chain {X : Type*} {A : X → X → Prop} {S : X → Prop}
    {p : List X} {s t : X} (hc : p.IsChain A)
    (hs : p.head? = some s) (ht : p.getLast? = some t)
    (hm : ∀ x ∈ p, S x) : Reach A S s t := by
  cases p with
  | nil => simp at hs
  | cons a tail =>
    simp only [List.head?_cons,Option.some.injEq] at hs
    subst a
    have hc' : (s :: tail).IsChain (Edge A S) :=
      hc.imp_of_mem_imp (fun x y hx hy h => ⟨h,hm x hx,hm y hy⟩)
    apply List.relationReflTransGen_of_exists_isChain_cons tail hc'
    simpa only [List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _),
      Option.some.injEq] using ht

/-- Removing loops from a restricted walk preserves its region and endpoints. -/
theorem simple {X : Type*} {A : X → X → Prop} {S : X → Prop} {s t : X}
    (hs : S s) (h : Reach A S s t) :
    ∃ p : List X, p.head? = some s ∧ p.getLast? = some t ∧
      p.IsChain A ∧ p.Nodup ∧ ∀ x ∈ p, S x := by
  classical
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[t],by simp,by simp,by simp,by simp,by simpa using hs⟩
  | @head a b hab h ih =>
    obtain ⟨p,hp,ht,hc,hn,hS⟩ := ih hab.2.2
    by_cases ha : a ∈ p
    · obtain ⟨pre,tail,rfl⟩ := List.mem_iff_append.mp ha
      refine ⟨a :: tail,by simp,?_,(List.isChain_append.mp hc).2.1,
        (List.nodup_append.mp hn).2.1,?_⟩
      · simpa using ht
      · intro x hx
        exact hS x (List.mem_append_right pre hx)
    · refine ⟨a :: p,by simp,?_,?_,by simp [ha,hn],?_⟩
      · cases p with
        | nil => simp at hp
        | cons b tail => simpa using ht
      · cases p with
        | nil => simp at hp
        | cons c tail =>
          simp only [List.head?_cons,Option.some.injEq] at hp
          subst c
          exact List.IsChain.cons_cons hab.1 hc
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hab.2.1
        · exact hS x hx

theorem disjoint_pair {X : Type*} {A : X → X → Prop} {S T : X → Prop}
    {s t u v : X} (hs : S s) (hu : T u)
    (hd : ∀ x, S x → T x → False)
    (hp : Reach A S s t) (hq : Reach A T u v) :
    ∃ p q : List X, p.head? = some s ∧ p.getLast? = some t ∧
      q.head? = some u ∧ q.getLast? = some v ∧
      p.IsChain A ∧ q.IsChain A ∧ p.Nodup ∧ q.Nodup ∧ p.Disjoint q := by
  obtain ⟨p,ps,pt,pc,pn,pm⟩ := simple hs hp
  obtain ⟨q,qs,qt,qc,qn,qm⟩ := simple hu hq
  refine ⟨p,q,ps,pt,qs,qt,pc,qc,pn,qn,?_⟩
  exact List.disjoint_left.mpr (fun x hx hy => hd x (pm x hx) (qm x hy))

end UnconstrainedPACDetection.RestrictedPaths

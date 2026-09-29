module

public import proofs.UnconstrainedPACDetection.DirectedPathNormalization
public import Mathlib.Data.List.Chain

@[expose] public section

namespace UnconstrainedPACDetection.ListSimplePaths
open DirectedPathNormalization

theorem of_list {X : Type*} {A : X → X → Prop} {s t : X} (hst : s ≠ t)
    {p : List X} (hc : p.IsChain A) (hn : p.Nodup)
    (hs : p.head? = some s) (ht : p.getLast? = some t) :
    ∃ P : SimplePath A s t, ∀ x ∈ P.vertices, x ∈ p := by
  cases p with
  | nil => simp at hs
  | cons a tail =>
    cases tail with
    | nil => simp at hs ht; exact False.elim (hst (hs.symm.trans ht))
    | cons b rest =>
      let f : Fin (rest.length+1+1) → X := fun i => (a::b::rest)[i.val]'(by have := i.isLt; simp; omega)
      have hfi : Function.Injective f := by
        intro i j h
        have h' := (List.nodup_iff_injective_get.mp hn)
          (show (a::b::rest).get ⟨i.val,by have := i.isLt; simp; omega⟩ =
            (a::b::rest).get ⟨j.val,by have := j.isLt; simp; omega⟩ from h)
        exact Fin.ext (congrArg Fin.val h')
      let P : SimplePath A s t := {
        length := rest.length+1
        positive := by omega
        vertex := f
        injective := hfi
        start := by simpa [f] using hs
        finish := by
          have he := List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil a (b::rest))
          rw [he] at ht
          simpa [f,List.getLast_eq_getElem] using ht
        edge := by
          intro i
          exact List.isChain_iff_getElem.mp hc i.val (by have := i.isLt; simp; omega) }
      refine ⟨P,?_⟩
      rintro x ⟨i,rfl⟩
      exact List.getElem_mem (by simpa [P] using i.isLt)

theorem to_list {X : Type*} {A : X → X → Prop} {s t : X} (P : SimplePath A s t) :
    ∃ p : List X, p.head? = some s ∧ p.getLast? = some t ∧
      p.IsChain A ∧ p.Nodup ∧ ∀ x ∈ p, x ∈ P.vertices := by
  refine ⟨List.ofFn P.vertex,?_,?_,?_,?_,?_⟩
  · simpa using congrArg some P.start
  · have hn : List.ofFn P.vertex ≠ [] := by simp
    rw [List.getLast?_eq_getLast_of_ne_nil hn,List.getLast_ofFn_succ]
    exact congrArg some P.finish
  · rw [List.isChain_iff_getElem]
    intro i hi
    have hi' : i < P.length := by simpa using hi
    simpa only [List.getElem_ofFn, Fin.castSucc_mk, Fin.succ_mk] using P.edge ⟨i,hi'⟩
  · exact List.nodup_ofFn.mpr P.injective
  · intro x hx
    exact (List.mem_ofFn' P.vertex x).mp hx

end UnconstrainedPACDetection.ListSimplePaths

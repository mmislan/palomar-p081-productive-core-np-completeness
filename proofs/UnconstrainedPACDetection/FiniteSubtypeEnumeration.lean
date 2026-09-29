module

public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.List.Dedup

@[expose] public section

namespace UnconstrainedPACDetection.FiniteSubtypeEnumeration

def selected {X : Type*} [DecidableEq X] (l : List X) (P : X → Prop) [DecidablePred P] :
    List {x // P x} :=
  (l.filterMap fun x => if h : P x then some ⟨x,h⟩ else none).dedup

theorem mem_selected {X : Type*} [DecidableEq X] (l : List X) (P : X → Prop)
    [DecidablePred P] (x : {x // P x}) : x ∈ selected l P ↔ x.val ∈ l := by
  rcases x with ⟨x,hx⟩
  simp only [selected,List.mem_dedup,List.mem_filterMap]
  constructor
  · rintro ⟨y,hy,he⟩
    split at he
    · cases Option.some.inj he
      exact hy
    · simp at he
  · intro h
    exact ⟨x,h,by simp [hx]⟩

theorem nodup_selected {X : Type*} [DecidableEq X] (l : List X) (P : X → Prop)
    [DecidablePred P] : (selected l P).Nodup := List.nodup_dedup _

theorem length_selected {X : Type*} [DecidableEq X] (l : List X) (P : X → Prop)
    [DecidablePred P] : (selected l P).length ≤ l.length :=
  (List.dedup_sublist _).length_le.trans (List.length_filterMap_le _ _)

end UnconstrainedPACDetection.FiniteSubtypeEnumeration

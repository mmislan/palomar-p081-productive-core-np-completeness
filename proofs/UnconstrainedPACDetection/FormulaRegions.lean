module

public import proofs.UnconstrainedPACDetection.FormulaWiring
public import proofs.UnconstrainedPACDetection.RestrictedPaths

@[expose] public section

namespace UnconstrainedPACDetection.FormulaRegions
open Complexity.SAT FormulaWiring ControlSwitch SwitchStack

def up (b : Bool) : List V := if b then leftUp else rightUp
def down (b : Bool) : List V := if b then leftDown else rightDown
def data (b : Bool) : List V := if b then leftData else rightData

def regionP (φ : CNF) (mode : Fin (levels φ) → Bool) : Vertex φ → Prop
  | .inl (i,a) => a ∈ down (mode i) ∨ a ∈ data (mode i)
  | .inr _ => True
def regionQ (φ : CNF) (mode : Fin (levels φ) → Bool) : Vertex φ → Prop
  | .inl (i,a) => a ∈ up (mode i)
  | .inr _ => False

theorem regions_disjoint (φ : CNF) (mode : Fin (levels φ) → Bool) (x : Vertex φ) :
    regionP φ mode x → regionQ φ mode x → False := by
  cases x with
  | inr x => simp [regionQ]
  | inl x =>
    obtain ⟨i,a⟩ := x
    have h : (up (mode i)).Disjoint (down (mode i)) ∧
        (data (mode i)).Disjoint (up (mode i) ++ down (mode i)) := by
      cases mode i
      · exact right_mode.2.2.2
      · exact left_mode.2.2.2
    intro hp hq
    rcases hp with hp | hp
    · exact List.disjoint_left.mp h.1 hq hp
    · exact List.disjoint_left.mp h.2 hp (List.mem_append_left _ hq)

theorem up_path (b : Bool) : Path 0 4 (up b) := by
  cases b
  · exact right_mode.1
  · exact left_mode.1
theorem down_path (b : Bool) : Path 1 5 (down b) := by
  cases b
  · exact right_mode.2.1
  · exact left_mode.2.1
theorem data_path (b : Bool) :
    Path (if b then 2 else 3) (if b then 6 else 7) (data b) := by
  cases b
  · exact right_mode.2.2.1
  · exact left_mode.2.2.1

theorem local_reach (φ : CNF) (S : Vertex φ → Prop) (i : Fin (levels φ))
    {a b : V} {p : List V} (hp : Path a b p)
    (hm : ∀ x ∈ p, S (sw i x)) :
    RestrictedPaths.Reach (adjacency φ) S (sw i a) (sw i b) := by
  apply RestrictedPaths.of_chain (p := p.map (sw i))
  · apply (List.isChain_map (sw i)).mpr
    apply ((SwitchSegments.follows_iff_chain p).mp hp.2.2.2).imp
    intro x y h
    exact Or.inl ⟨rfl,h⟩
  · simpa using congrArg (Option.map (sw (X := External φ) i)) hp.1
  · simpa using congrArg (Option.map (sw (X := External φ) i)) hp.2.1
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact hm a ha

theorem down_reach (φ : CNF) (mode : Fin (levels φ) → Bool) (i : Fin (levels φ)) :
    RestrictedPaths.Reach (adjacency φ) (regionP φ mode) (sw i 1) (sw i 5) :=
  local_reach φ _ i (down_path (mode i)) (fun _ h => Or.inl h)

theorem up_reach (φ : CNF) (mode : Fin (levels φ) → Bool) (i : Fin (levels φ)) :
    RestrictedPaths.Reach (adjacency φ) (regionQ φ mode) (sw i 0) (sw i 4) :=
  local_reach φ _ i (up_path (mode i)) (fun _ h => h)

theorem data_reach (φ : CNF) (mode : Fin (levels φ) → Bool) (i : Fin (levels φ)) :
    RestrictedPaths.Reach (adjacency φ) (regionP φ mode)
      (sw i (if mode i then 2 else 3)) (sw i (if mode i then 6 else 7)) :=
  local_reach φ _ i (data_path (mode i)) (fun _ h => Or.inr h)

end UnconstrainedPACDetection.FormulaRegions

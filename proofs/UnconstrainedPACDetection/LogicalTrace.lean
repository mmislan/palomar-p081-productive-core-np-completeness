module

public import proofs.UnconstrainedPACDetection.FormulaWiring

@[expose] public section

namespace UnconstrainedPACDetection.LogicalTrace
open FormulaWiring SwitchStack ControlSwitch

def rank (φ : Complexity.SAT.CNF) : External φ → Nat
  | .var v => v.val * (levels φ + 2)
  | .rail v _ j => v.val * (levels φ + 2) + j.val + 1
  | .clause c => varCount φ * (levels φ + 2) + c.val + 1

theorem blocked_lookup (φ : Complexity.SAT.CNF) (i : Fin (levels φ))
    (v : Fin (varCount φ)) (b : Bool) :
    blocked φ i v b = true ↔ ∃ j l, lookup φ i = some (j,l) ∧ l.var = v.val ∧ l.sign ≠ b := by
  cases h : lookup φ i with
  | none => simp [blocked,h]
  | some o => obtain ⟨j,l⟩ := o; simp [blocked,h]

theorem blocked_unique (φ : Complexity.SAT.CNF) (i : Fin (levels φ))
    {v w : Fin (varCount φ)} {b c : Bool}
    (hv : blocked φ i v b = true) (hw : blocked φ i w c = true) : v = w ∧ b = c := by
  obtain ⟨j,l,hl,hv,hb⟩ := (blocked_lookup φ i v b).mp hv
  obtain ⟨j',l',hl',hw,hc⟩ := (blocked_lookup φ i w c).mp hw
  have he := Option.some.inj (hl.symm.trans hl')
  cases he
  refine ⟨Fin.ext (hv.symm.trans hw),?_⟩
  cases l.sign <;> cases b <;> cases c <;> simp_all

/-- A direct external wire or one complete straight residual switch visit.
This relation retains the physical occurrence shared by its two attachments. -/
def Step (φ : Complexity.SAT.CNF) (x y : External φ) : Prop :=
  adjacency φ (Sum.inr x) (Sum.inr y) ∨
  ∃ i a b, DataWire φ (Sum.inr x) (sw i a) ∧
    ((a = 2 ∧ b = 6) ∨ (a = 3 ∧ b = 7)) ∧ DataWire φ (sw i b) (Sum.inr y)

theorem direct_rank (φ : Complexity.SAT.CNF) (x y : External φ)
    (h : adjacency φ (Sum.inr x) (Sum.inr y)) : rank φ y = rank φ x + 1 := by
  cases x <;> cases y <;> simp [adjacency,Edge,DataWire] at h
  all_goals simp_all [rank,Nat.add_mul]
  all_goals omega

theorem left_rank (φ : Complexity.SAT.CNF) (i : Fin (levels φ)) (x y : External φ)
    (hx : DataWire φ (Sum.inr x) (sw i 2)) (hy : DataWire φ (sw i 6) (Sum.inr y)) :
    rank φ y = rank φ x + 1 := by
  cases x <;> cases y <;> simp [DataWire,sw] at hx hy
  obtain ⟨l,hl⟩ := hx
  obtain ⟨j,⟨l',hl'⟩,hc⟩ := hy
  have he := Option.some.inj (hl.symm.trans hl')
  have hj := congrArg Prod.fst he
  simp only [rank]
  omega

theorem right_rank (φ : Complexity.SAT.CNF) (i : Fin (levels φ)) (x y : External φ)
    (hx : DataWire φ (Sum.inr x) (sw i 3)) (hy : DataWire φ (sw i 7) (Sum.inr y)) :
    rank φ y = rank φ x + 1 := by
  cases x <;> cases y <;> simp [DataWire,sw] at hx hy
  obtain ⟨hj,hb⟩ := hx
  obtain ⟨hk,hc⟩ := hy
  obtain ⟨hv,he⟩ := blocked_unique φ i hb hc
  subst hv; subst he
  simp only [rank]
  omega

theorem step_rank (φ : Complexity.SAT.CNF) {x y : External φ} (h : Step φ x y) :
    rank φ y = rank φ x + 1 := by
  rcases h with h | ⟨i,a,b,hx,hmode,hy⟩
  · exact direct_rank φ x y h
  · rcases hmode with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact left_rank φ i x y hx hy
    · exact right_rank φ i x y hx hy

/-- Contiguous extraction retains the remainder required by trace induction.
The local visit ends at the first boundary output, not at the first vertex
outside the switch. Complete control avoidance is a stated input. -/
theorem visit_prefix (φ : Complexity.SAT.CNF) (i : Fin (levels φ))
    {a : V} {tail : List (Vertex φ)} {t : External φ} {up down : List V}
    (hc : (sw i a :: tail).IsChain (adjacency φ))
    (hn : (sw i a :: tail).Nodup)
    (he : (sw i a :: tail).getLast? = some (Sum.inr t))
    (hu : Path 0 4 up) (hd : Path 1 5 down) (hud : up.Disjoint down)
    (havoid : ∀ v ∈ up ++ down, sw i v ∉ sw i a :: tail)
    (ha : input a) :
    ∃ b segment rest, Path a b segment ∧
      segment.map (sw i) ++ rest = sw i a :: tail ∧
      ((a = 2 ∧ b = 6) ∨ (a = 3 ∧ b = 7)) := by
  obtain ⟨b,segment,rest,hb,hh,hl,hchain,heq⟩ :=
    SwitchSegments.boundary_prefix (sw i) (adjacency φ) (fun x y => y ∈ next x)
      output (restrict_out (DataWire φ) i) (exits (DataWire φ) i) a tail hc
      (by intro b hb; rw [he] at hb; simp [sw] at hb)
  have hmap : (segment.map (sw (X := External φ) i)).Nodup := by
    have h : (segment.map (sw i) ++ rest).Nodup := heq.symm ▸ hn
    exact h.of_append_left
  have hp : Path a b segment :=
    ⟨hh,hl,List.Nodup.of_map (sw i) hmap,(SwitchSegments.follows_iff_chain _).mpr hchain⟩
  have hsub : ∀ v ∈ segment, sw i v ∈ sw i a :: tail := by
    intro v hv
    rw [← heq]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨v,hv,rfl⟩)
  exact ⟨b,segment,rest,hp,heq,ResidualSuffix.data_channel i hu hd hud havoid ha hb hp hsub⟩

end UnconstrainedPACDetection.LogicalTrace

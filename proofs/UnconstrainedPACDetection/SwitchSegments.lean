module

public import proofs.UnconstrainedPACDetection.ControlSwitch
public import Mathlib.Data.List.Chain

@[expose] public section

namespace UnconstrainedPACDetection.SwitchSegments

open ControlSwitch

theorem boundary_prefix {X : Type*} (embed : V → X) (A : X → X → Prop)
    (R : V → V → Prop) (out : V → Prop)
    (restrict : ∀ a b, ¬out a → A (embed a) (embed b) → R a b)
    (exit : ∀ a y, A (embed a) y → (∀ b, y ≠ embed b) → out a)
    (a : V) (tail : List X) (hc : (embed a :: tail).IsChain A)
    (hend : ∀ b, (embed a :: tail).getLast? = some (embed b) → out b) :
    ∃ (b : V) (segment : List V) (rest : List X), out b ∧ segment.head? = some a ∧ segment.getLast? = some b ∧
      segment.IsChain R ∧ segment.map embed ++ rest = embed a :: tail := by
  classical
  induction tail generalizing a with
  | nil => exact ⟨a,[a],[],hend a rfl,rfl,rfl,.singleton _,rfl⟩
  | cons x tail ih =>
    by_cases ho : out a
    · exact ⟨a,[a],x::tail,ho,rfl,rfl,.singleton _,rfl⟩
    · have hc' := List.isChain_cons_cons.mp hc
      by_cases hx : ∃ b, embed b = x
      · obtain ⟨b,rfl⟩ := hx
        obtain ⟨c,segment,rest,hout,hh,hl,hchain,heq⟩ := ih b hc'.2 (by
          intro v hv
          apply hend v
          simpa only [List.getLast?_cons_cons] using hv)
        cases segment with
        | nil => simp at hh
        | cons d segment =>
          have hd : d = b := by simpa using hh
          subst d
          refine ⟨c,a::b::segment,rest,hout,rfl,?_,?_,?_⟩
          · simpa only [List.getLast?_cons_cons] using hl
          · exact List.isChain_cons_cons.mpr ⟨restrict a b ho hc'.1,hchain⟩
          · simpa only [List.map_cons,List.cons_append] using congrArg (embed a :: ·) heq
      · exact ⟨a,[a],x::tail,exit a x hc'.1 (fun b h => hx ⟨b,h.symm⟩),
          rfl,rfl,.singleton _,rfl⟩

theorem segment_from_mem {X : Type*} (embed : V → X) (A : X → X → Prop)
    (R : V → V → Prop) (out : V → Prop)
    (restrict : ∀ a b, ¬out a → A (embed a) (embed b) → R a b)
    (exit : ∀ a y, A (embed a) y → (∀ b, y ≠ embed b) → out a)
    {a : V} {p : List X} (hc : p.IsChain A) (hnd : p.Nodup)
    (hend : ∀ b, p.getLast? = some (embed b) → out b) (hm : embed a ∈ p) :
    ∃ (b : V) (segment : List V), out b ∧ segment.head? = some a ∧ segment.getLast? = some b ∧
      segment.Nodup ∧ segment.IsChain R ∧ ∀ v ∈ segment, embed v ∈ p := by
  obtain ⟨pre,tail,rfl⟩ := List.mem_iff_append.mp hm
  have hs := (List.isChain_split.mp hc).2
  obtain ⟨b,segment,rest,hb,hh,hl,hchain,heq⟩ :=
    boundary_prefix embed A R out restrict exit a tail hs (by
      intro v hv
      apply hend v
      simpa using hv)
  have hmap : (segment.map embed).Nodup := by
    have h : (segment.map embed ++ rest).Nodup := by
      rw [heq]
      exact hnd.of_append_right
    exact h.of_append_left
  refine ⟨b,segment,hb,hh,hl,List.Nodup.of_map embed hmap,hchain,?_⟩
  intro v hv
  apply List.mem_append_right
  rw [← heq]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨v,hv,rfl⟩)

theorem follows_iff_chain (p : List V) :
    follows p ↔ p.IsChain (fun a b => b ∈ next a) := by
  induction p using List.twoStepInduction with
  | nil => simp [follows]
  | singleton a => simp [follows]
  | cons_cons a b p _ ih => simpa [follows] using and_congr Iff.rfl (ih b)

theorem exit_path {X : Type*} (embed : V → X) (A : X → X → Prop)
    (out : V → Prop)
    (restrict : ∀ a b, ¬out a → A (embed a) (embed b) → b ∈ next a)
    (exit : ∀ a y, A (embed a) y → (∀ b, y ≠ embed b) → out a)
    {a : V} {p : List X} (hc : p.IsChain A) (hnd : p.Nodup)
    (hend : ∀ b, p.getLast? = some (embed b) → out b) (hm : embed a ∈ p) :
    ∃ (b : V) (segment : List V), out b ∧ Path a b segment ∧
      ∀ v ∈ segment, embed v ∈ p := by
  obtain ⟨b,segment,hb,hh,hl,hn,hc,hs⟩ :=
    segment_from_mem embed A _ out restrict exit hc hnd hend hm
  exact ⟨b,segment,hb,⟨hh,hl,hn,(follows_iff_chain _).mpr hc⟩,hs⟩

theorem entry_path {X : Type*} (embed : V → X) (A : X → X → Prop)
    (inp : V → Prop)
    (restrict : ∀ a b, ¬inp a → A (embed b) (embed a) → a ∈ next b)
    (entry : ∀ a y, A y (embed a) → (∀ b, y ≠ embed b) → inp a)
    {b : V} {p : List X} (hc : p.IsChain A) (hnd : p.Nodup)
    (hstart : ∀ a, p.head? = some (embed a) → inp a) (hm : embed b ∈ p) :
    ∃ (a : V) (segment : List V), inp a ∧ Path a b segment ∧
      ∀ v ∈ segment, embed v ∈ p := by
  obtain ⟨a,segment,ha,hh,hl,hn,hc,hs⟩ :=
    segment_from_mem embed (fun x y => A y x) (fun x y => x ∈ next y) inp
      restrict entry (List.isChain_reverse.mpr hc) (by simpa using hnd)
      (by simpa using hstart) (by simpa using hm)
  refine ⟨a,segment.reverse,ha,?_,?_⟩
  · refine ⟨by simpa using hl,by simpa using hh,by simpa using hn,?_⟩
    apply (follows_iff_chain _).mpr
    exact List.isChain_reverse.mpr hc
  · intro v hv
    have h := hs v (by simpa using hv)
    simpa using h

theorem head_mem {X : Type*} {p : List X} {a : X} (h : p.head? = some a) : a ∈ p := by
  cases p with
  | nil => simp at h
  | cons b p =>
    have hb : b = a := by simpa using h
    simp [hb]

theorem last_mem {X : Type*} {p : List X} {a : X} (h : p.getLast? = some a) : a ∈ p := by
  have h' : p.reverse.head? = some a := by simpa using h
  simpa using head_mem h'

theorem successor {X : Type*} {A : X → X → Prop} {p : List X} {a : X}
    (hc : p.IsChain A) (hm : a ∈ p) (hl : p.getLast? ≠ some a) :
    ∃ b, A a b ∧ b ∈ p := by
  obtain ⟨pre,tail,rfl⟩ := List.mem_iff_append.mp hm
  cases tail with
  | nil => simp at hl
  | cons b tail =>
    exact ⟨b,(List.isChain_cons_cons.mp (List.isChain_split.mp hc).2).1,by simp⟩

theorem predecessor {X : Type*} {A : X → X → Prop} {p : List X} {a : X}
    (hc : p.IsChain A) (hm : a ∈ p) (hh : p.head? ≠ some a) :
    ∃ b, A b a ∧ b ∈ p := by
  obtain ⟨b,hb,hm⟩ := successor (A := fun x y => A y x)
    (List.isChain_reverse.mpr hc) (by simpa using hm) (by simpa using hh)
  exact ⟨b,hb,by simpa using hm⟩

end UnconstrainedPACDetection.SwitchSegments

module

public import proofs.UnconstrainedPACDetection.LogicalSuffix

@[expose] public section

namespace UnconstrainedPACDetection.ResidualSuffix
open ControlSwitch SwitchSegments SwitchStack LogicalSuffix

/-- Extract complete local controls from the actual closed prefix and descending
path. Every vertex of either control is unavailable to the logical suffix. -/
theorem controls_in_prefix {n : Nat} {X : Type*}
    (W : Node n X → Node n X → Prop) (i : Fin n)
    {ctrl q suffix : List (Node n X)}
    (hp : ctrl.IsChain (Edge W)) (hq : q.IsChain (Edge W))
    (hpn : ctrl.Nodup) (hqn : q.Nodup) (hd : ctrl.Disjoint q)
    (hcs : ctrl.Disjoint suffix) (hqsuf : q.Disjoint suffix)
    (hpe : ∀ b, ctrl.getLast? = some (sw i b) → output b)
    (hqs : ∀ a, q.head? = some (sw i a) → input a)
    (hb : sw i 1 ∈ ctrl) (ha : sw i 4 ∈ q) :
    ∃ up down : List V,
      Path 0 4 up ∧ Path 1 5 down ∧ up.Disjoint down ∧
      (∀ v ∈ up, sw i v ∈ q) ∧ (∀ v ∈ down, sw i v ∈ ctrl) ∧
      (∀ v ∈ up ++ down, sw i v ∉ suffix) := by
  obtain ⟨b,down,hb',hdown,hdownsub⟩ := exit_path (sw i) (Edge W) output
    (restrict_out W i) (exits W i) hp hpn hpe hb
  obtain ⟨a,up,ha',hup,hupsub⟩ := entry_path (sw i) (Edge W) input
    (restrict_in W i) (enters W i) hq hqn hqs ha
  have hdis : up.Disjoint down := by
    intro v hu hv
    exact hd (hdownsub v hv) (hupsub v hu)
  obtain ⟨rfl,rfl⟩ := control_ports ha' hb' hup hdown hdis
  refine ⟨up,down,hup,hdown,hdis,hupsub,hdownsub,?_⟩
  intro v hv hm
  rcases List.mem_append.mp hv with hu | hd'
  · exact hqsuf (hupsub v hu) hm
  · exact hcs (hdownsub v hd') hm

/-- The exact cut supplies whole control paths, not merely avoided ports. -/
theorem suffix_has_controls {n : Nat} {X : Type*} (hn : 0 < n)
    (W : Node n X → Node n X → Prop) {p q : List (Node n X)} {t : X}
    (hp : p.IsChain (Edge W)) (hq : q.IsChain (Edge W))
    (hpn : p.Nodup) (hqn : q.Nodup) (hd : p.Disjoint q)
    (hps : p.head? = some (sw ⟨0,hn⟩ 1)) (hpe : p.getLast? = some (Sum.inr t))
    (hqs : q.head? = some (sw ⟨n-1,by omega⟩ 0))
    (hqe : q.getLast? = some (sw ⟨0,hn⟩ 4)) :
    ∃ pre suffix : List (Node n X),
      p = pre ++ [sw ⟨n-1,by omega⟩ 5] ++ suffix ∧
      (∀ i : Fin n, ∃ up down : List V,
        Path 0 4 up ∧ Path 1 5 down ∧ up.Disjoint down ∧
        (∀ v ∈ up, sw i v ∈ q) ∧
        (∀ v ∈ down, sw i v ∈ pre ++ [sw ⟨n-1,by omega⟩ 5]) ∧
        (∀ v ∈ up ++ down, sw i v ∉ suffix)) := by
  obtain ⟨pre,suffix,heq,hports,_⟩ :=
    logical_suffix_avoids_controls hn W hp hq hpn hqn hd hps hpe hqs hqe
  have hall := all_control_ports hn W hp hq hpn hqn hd hps hpe hqs hqe
  let ctrl := pre ++ [sw (X := X) ⟨n-1,by omega⟩ 5]
  have heq' : p = ctrl ++ suffix := heq
  have hcs : ctrl.Disjoint suffix := by
    intro v hv hs
    exact (List.nodup_append.mp (heq' ▸ hpn)).2.2 v hv v hs rfl
  have hcq : ctrl.Disjoint q := by
    intro v hv hq'
    apply hd _ hq'
    rw [heq']
    exact List.mem_append_left _ hv
  have hqsuf : q.Disjoint suffix := by
    intro v hq' hs
    apply hd _ hq'
    rw [heq']
    exact List.mem_append_right _ hs
  have hctrl : ctrl.IsChain (Edge W) := by
    have hp' : (pre ++ sw (X := X) ⟨n-1,by omega⟩ 5 :: suffix).IsChain (Edge W) := by
      have h : (pre ++ [sw (X := X) ⟨n-1,by omega⟩ 5] ++ suffix).IsChain (Edge W) := heq ▸ hp
      simpa using h
    exact (List.isChain_split.mp hp').1
  refine ⟨pre,suffix,heq,?_⟩
  intro i
  apply controls_in_prefix W i hctrl hq (heq' ▸ hpn).of_append_left hqn hcq hcs hqsuf
  · intro b hb
    simp [ctrl,sw] at hb
    simp [output,← hb.2]
  · intro a ha
    rw [hqs] at ha
    simp [sw] at ha
    simp [input,← ha.2]
  · exact (hports i).1
  · exact (hall i).2.2.2

theorem data_channel {n : Nat} {X : Type*} (i : Fin n)
    {suffix : List (Node n X)} {up down segment : List V} {a b : V}
    (hu : Path 0 4 up) (hd : Path 1 5 down) (hud : up.Disjoint down)
    (havoid : ∀ v ∈ up ++ down, sw i v ∉ suffix)
    (ha : input a) (hb : output b) (ht : Path a b segment)
    (hsub : ∀ v ∈ segment, sw i v ∈ suffix) :
    (a = 2 ∧ b = 6) ∨ (a = 3 ∧ b = 7) := by
  apply residual_channel hu hd hud ha hb ht
  · intro v hv hs
    exact havoid v (List.mem_append_left _ hs) (hsub v hv)
  · intro v hv hs
    exact havoid v (List.mem_append_right _ hs) (hsub v hv)

theorem data_exclusive {n : Nat} {X : Type*} (i : Fin n)
    {suffix : List (Node n X)} {up down left right : List V}
    (hu : Path 0 4 up) (hd : Path 1 5 down) (hud : up.Disjoint down)
    (havoid : ∀ v ∈ up ++ down, sw i v ∉ suffix)
    (hl : Path 2 6 left) (hr : Path 3 7 right)
    (hleft : ∀ v ∈ left, sw i v ∈ suffix)
    (hright : ∀ v ∈ right, sw i v ∈ suffix) : False := by
  apply residual_exclusive hu hd hud hl hr
  · intro v hv hs; exact havoid v (List.mem_append_left _ hs) (hleft v hv)
  · intro v hv hs; exact havoid v (List.mem_append_right _ hs) (hleft v hv)
  · intro v hv hs; exact havoid v (List.mem_append_left _ hs) (hright v hv)
  · intro v hv hs; exact havoid v (List.mem_append_right _ hs) (hright v hv)

theorem extract_data_visit {n : Nat} {X : Type*}
    (W : Node n X → Node n X → Prop) (i : Fin n)
    {suffix : List (Node n X)} {up down : List V} {a : V} {t : X}
    (hc : suffix.IsChain (Edge W)) (hn : suffix.Nodup)
    (he : suffix.getLast? = some (Sum.inr t))
    (hu : Path 0 4 up) (hd : Path 1 5 down) (hud : up.Disjoint down)
    (havoid : ∀ v ∈ up ++ down, sw i v ∉ suffix)
    (ha : input a) (hm : sw i a ∈ suffix) :
    ∃ (b : V) (segment : List V), Path a b segment ∧
      (∀ v ∈ segment, sw i v ∈ suffix) ∧
      ((a = 2 ∧ b = 6) ∨ (a = 3 ∧ b = 7)) := by
  obtain ⟨b,segment,hb,ht,hsub⟩ := exit_path (sw i) (Edge W) output
    (restrict_out W i) (exits W i) hc hn (by intro b hb; rw [he] at hb; simp [sw] at hb) hm
  exact ⟨b,segment,ht,hsub,data_channel i hu hd hud havoid ha hb ht hsub⟩

/-- The same logical suffix cannot visit both data entrances of a switch. -/
theorem data_inputs_exclusive {n : Nat} {X : Type*}
    (W : Node n X → Node n X → Prop) (i : Fin n)
    {suffix : List (Node n X)} {up down : List V} {t : X}
    (hc : suffix.IsChain (Edge W)) (hn : suffix.Nodup)
    (he : suffix.getLast? = some (Sum.inr t))
    (hu : Path 0 4 up) (hd : Path 1 5 down) (hud : up.Disjoint down)
    (havoid : ∀ v ∈ up ++ down, sw i v ∉ suffix)
    (hl : sw i 2 ∈ suffix) (hr : sw i 3 ∈ suffix) : False := by
  obtain ⟨b,left,hleft,hsleft,hbl⟩ := extract_data_visit W i hc hn he hu hd hud havoid
    (a := 2) (by simp [input]) hl
  obtain ⟨c,right,hright,hsright,hcr⟩ := extract_data_visit W i hc hn he hu hd hud havoid
    (a := 3) (by simp [input]) hr
  have hb : b = 6 := by simpa using hbl
  have hc' : c = 7 := by simpa using hcr
  subst b; subst c
  exact data_exclusive i hu hd hud havoid hleft hright hsleft hsright

/-- Direct consequence for an arbitrary accepted pair: after the top exit,
no switch has both logical data entrances visited. -/
theorem logical_suffix_exclusive {n : Nat} {X : Type*} (hn : 0 < n)
    (W : Node n X → Node n X → Prop) {p q : List (Node n X)} {t : X}
    (hp : p.IsChain (Edge W)) (hq : q.IsChain (Edge W))
    (hpn : p.Nodup) (hqn : q.Nodup) (hd : p.Disjoint q)
    (hps : p.head? = some (sw ⟨0,hn⟩ 1)) (hpe : p.getLast? = some (Sum.inr t))
    (hqs : q.head? = some (sw ⟨n-1,by omega⟩ 0))
    (hqe : q.getLast? = some (sw ⟨0,hn⟩ 4)) :
    ∃ pre suffix : List (Node n X),
      p = pre ++ [sw ⟨n-1,by omega⟩ 5] ++ suffix ∧
      (∀ i : Fin n, ¬(sw i 2 ∈ suffix ∧ sw i 3 ∈ suffix)) := by
  obtain ⟨pre,suffix,heq,hcontrols⟩ :=
    suffix_has_controls hn W hp hq hpn hqn hd hps hpe hqs hqe
  have hpn' : ((pre ++ [sw (X := X) ⟨n-1,by omega⟩ 5]) ++ suffix).Nodup := heq ▸ hpn
  have hsnd : suffix.Nodup := hpn'.of_append_right
  have hchain : suffix.IsChain (Edge W) := by
    have h : (pre ++ sw (X := X) ⟨n-1,by omega⟩ 5 :: suffix).IsChain (Edge W) := by
      have h' : (pre ++ [sw (X := X) ⟨n-1,by omega⟩ 5] ++ suffix).IsChain (Edge W) := heq ▸ hp
      simpa using h'
    exact (List.isChain_split.mp h).2.tail
  have hlast : suffix.getLast? = some (Sum.inr t) := by
    rw [heq] at hpe
    cases suffix with
    | nil => simp [sw] at hpe
    | cons x xs => simpa using hpe
  refine ⟨pre,suffix,heq,?_⟩
  intro i ⟨hl,hr⟩
  obtain ⟨up,down,hu,hdown,hdis,_,_,havoid⟩ := hcontrols i
  exact data_inputs_exclusive W i hchain hsnd hlast hu hdown hdis havoid hl hr

end UnconstrainedPACDetection.ResidualSuffix

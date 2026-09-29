module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Nodup
public import Mathlib.Tactic

@[expose] public section

namespace UnconstrainedPACDetection.ControlSwitch

abbrev V := Fin 20

def edges : List (V × V) :=
  [(0,9),(0,15),(1,17),(1,18),(2,8),(3,12),(8,5),(8,9),
   (9,10),(9,11),(10,8),(10,11),(11,6),(11,19),(12,13),(13,5),
   (13,14),(14,12),(14,15),(15,7),(15,16),(16,4),(16,10),
   (17,4),(17,18),(18,16),(18,19),(19,14),(19,17)]

def next (a : V) : List V := (edges.filter fun e => e.1 == a).map Prod.snd

def follows : List V → Prop
  | [] => True
  | [_] => True
  | a :: b :: p => b ∈ next a ∧ follows (b :: p)

def enumerate : Nat → List V → V → List (List V)
  | 0, _, _ => []
  | n+1, seen, a => if a ∈ seen then [] else
      [ [a] ] ++ (next a).flatMap (fun b => (enumerate n (a::seen) b).map (a :: ·))

theorem enumerate_complete (n : Nat) (a : V) (tail seen : List V)
    (hn : (a::tail).length ≤ n) (hnd : (a::tail).Nodup)
    (hd : (a::tail).Disjoint seen) (hf : follows (a::tail)) :
    a::tail ∈ enumerate n seen a := by
  induction n generalizing a tail seen with
  | zero => simp at hn
  | succ n ih =>
    have ha : a ∉ seen := fun h => hd List.mem_cons_self h
    simp only [enumerate, ite_eq_right ha, List.mem_append]
    cases tail with
    | nil => exact Or.inl (by simp)
    | cons b tail =>
      right
      have htail : (b::tail).Disjoint (a::seen) := by
        intro x hx hmem
        rcases List.mem_cons.mp hmem with h | h
        · subst x
          exact (List.nodup_cons.mp hnd).1 hx
        · exact hd (List.mem_cons_of_mem _ hx) h
      have ht := ih b tail (a::seen) (by simpa using Nat.le_of_succ_le_succ hn)
        (List.nodup_cons.mp hnd).2 htail hf.2
      exact List.mem_flatMap.mpr ⟨b,hf.1,List.mem_map.mpr ⟨b::tail,ht,rfl⟩⟩

def routes (a b : V) : List (List V) :=
  (enumerate 20 [] a).filter fun p => p.getLast? == some b

def Path (a b : V) (p : List V) : Prop :=
  p.head? = some a ∧ p.getLast? = some b ∧ p.Nodup ∧ follows p

theorem path_mem_routes {a b : V} {p : List V} (hp : Path a b p) : p ∈ routes a b := by
  obtain ⟨hs,he,hnd,hf⟩ := hp
  cases p with
  | nil => simp at hs
  | cons x tail =>
    have hx : x = a := by simpa using hs
    subst x
    apply List.mem_filter.mpr
    refine ⟨enumerate_complete 20 a tail [] ?_ hnd (by simp) hf, ?_⟩
    · simpa using hnd.length_le_card
    · simpa using he

def separate (p q : List V) : Bool := p.all fun x => !q.contains x

theorem separate_iff (p q : List V) : separate p q = true ↔ p.Disjoint q := by
  simp [separate, List.disjoint_left]

def controlCheck : Bool :=
  ([0,1,2,3] : List V).all fun a => ([4,5,6,7] : List V).all fun b =>
    (routes a 4).all fun p => (routes 1 b).all fun q =>
      !separate p q || (a == 0 && b == 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem controlCheck_true : controlCheck = true := by decide

theorem control_ports_checked :
    ∀ a ∈ ([0,1,2,3] : List V), ∀ b ∈ ([4,5,6,7] : List V),
    ∀ p ∈ routes a 4, ∀ q ∈ routes 1 b,
    p.Disjoint q → a = 0 ∧ b = 5 := by
  intro a ha b hb p hp q hq hd
  have h := List.all_eq_true.mp controlCheck_true a ha
  have h := List.all_eq_true.mp h b hb
  have h := List.all_eq_true.mp h p hp
  have h := List.all_eq_true.mp h q hq
  simpa [(separate_iff p q).mpr hd] using h

theorem control_ports {a b : V} {p q : List V}
    (ha : a ∈ ([0,1,2,3] : List V)) (hb : b ∈ ([4,5,6,7] : List V))
    (hp : Path a 4 p) (hq : Path 1 b q) (hd : p.Disjoint q) : a = 0 ∧ b = 5 :=
  control_ports_checked a ha b hb p (path_mem_routes hp) q (path_mem_routes hq) hd

def usable (p q t : List V) : Bool := separate t p && separate t q

def residualCheck : Bool :=
  (routes 0 4).all fun p => (routes 1 5).all fun q =>
    !separate p q || (([0,1,2,3] : List V).all fun a =>
      ([4,5,6,7] : List V).all fun b => (routes a b).all fun t =>
        !usable p q t || ((a == 2 && b == 6) || (a == 3 && b == 7)))

def exclusiveCheck : Bool :=
  (routes 0 4).all fun p => (routes 1 5).all fun q =>
    !separate p q || !((routes 2 6).any (usable p q) && (routes 3 7).any (usable p q))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem residualCheck_true : residualCheck = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem exclusiveCheck_true : exclusiveCheck = true := by decide

theorem residual_channel {a b : V} {p q t : List V}
    (hp : Path 0 4 p) (hq : Path 1 5 q) (hd : p.Disjoint q)
    (ha : a ∈ ([0,1,2,3] : List V)) (hb : b ∈ ([4,5,6,7] : List V))
    (ht : Path a b t) (htp : t.Disjoint p) (htq : t.Disjoint q) :
    (a = 2 ∧ b = 6) ∨ (a = 3 ∧ b = 7) := by
  have h := List.all_eq_true.mp residualCheck_true p (path_mem_routes hp)
  have h := List.all_eq_true.mp h q (path_mem_routes hq)
  have hs := (separate_iff p q).mpr hd
  simp only [hs, Bool.not_true, Bool.false_or] at h
  have h := List.all_eq_true.mp h a ha
  have h := List.all_eq_true.mp h b hb
  have h := List.all_eq_true.mp h t (path_mem_routes ht)
  simpa [usable,(separate_iff t p).mpr htp,(separate_iff t q).mpr htq] using h

theorem residual_exclusive {p q t u : List V}
    (hp : Path 0 4 p) (hq : Path 1 5 q) (hd : p.Disjoint q)
    (ht : Path 2 6 t) (hu : Path 3 7 u)
    (htp : t.Disjoint p) (htq : t.Disjoint q)
    (hup : u.Disjoint p) (huq : u.Disjoint q) : False := by
  have h := List.all_eq_true.mp exclusiveCheck_true p (path_mem_routes hp)
  have h := List.all_eq_true.mp h q (path_mem_routes hq)
  have ht' : (routes 2 6).any (usable p q) = true := List.any_eq_true.mpr
    ⟨t,path_mem_routes ht,by simp [usable,(separate_iff t p).mpr htp,(separate_iff t q).mpr htq]⟩
  have hu' : (routes 3 7).any (usable p q) = true := List.any_eq_true.mpr
    ⟨u,path_mem_routes hu,by simp [usable,(separate_iff u p).mpr hup,(separate_iff u q).mpr huq]⟩
  simp [(separate_iff p q).mpr hd,ht',hu'] at h

def leftUp : List V := [0,15,16,4]
def leftDown : List V := [1,17,18,19,14,12,13,5]
def leftData : List V := [2,8,9,10,11,6]
def rightUp : List V := [0,9,11,19,17,4]
def rightDown : List V := [1,18,16,10,8,5]
def rightData : List V := [3,12,13,14,15,7]

theorem left_mode : Path 0 4 leftUp ∧ Path 1 5 leftDown ∧ Path 2 6 leftData ∧
    leftUp.Disjoint leftDown ∧ leftData.Disjoint (leftUp ++ leftDown) := by
  simp [Path,leftUp,leftDown,leftData,follows,next,edges,List.disjoint_left]

theorem right_mode : Path 0 4 rightUp ∧ Path 1 5 rightDown ∧ Path 3 7 rightData ∧
    rightUp.Disjoint rightDown ∧ rightData.Disjoint (rightUp ++ rightDown) := by
  simp [Path,rightUp,rightDown,rightData,follows,next,edges,List.disjoint_left]

end UnconstrainedPACDetection.ControlSwitch

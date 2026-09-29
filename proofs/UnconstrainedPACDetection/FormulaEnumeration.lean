module

public import proofs.UnconstrainedPACDetection.FormulaWiring
public import Mathlib.Data.List.ProdSigma

@[expose] public section

namespace UnconstrainedPACDetection.FormulaEnumeration
open Complexity.SAT FormulaWiring SwitchStack

/-- A finite Boolean implementation of the formula's literal wiring relation. -/
def wireTest (φ : CNF) : Vertex φ → Vertex φ → Bool
  | .inl (i,a), .inr (.var v) => a == 5 && i.val+1 == levels φ && v.val == 0
  | .inr (.var v), .inr (.rail w _ j) => v.val == w.val && j.val == 0
  | .inr (.rail v b j), .inr (.rail w c k) =>
      if hj : j.val < levels φ then
        v == w && b == c && k.val == j.val+1 && !blocked φ ⟨j.val,hj⟩ v b
      else false
  | .inr (.rail v b j), .inl (i,a) => a == 3 && j.val == i.val && blocked φ i v b
  | .inl (i,a), .inr (.rail v b j) => a == 7 && j.val == i.val+1 && blocked φ i v b
  | .inr (.rail v _ j), .inr (.var w) => j.val == levels φ && w.val == v.val+1
  | .inr (.var v), .inr (.clause c) => v.val == varCount φ && c.val == 0
  | .inr (.clause c), .inl (i,a) =>
      a == 2 && match lookup φ i with | none => false | some (j,_) => j == c.val
  | .inl (i,a), .inr (.clause c) =>
      a == 6 && match lookup φ i with | none => false | some (j,_) => c.val == j+1
  | _, _ => false

theorem wireTest_correct (φ : CNF) (x y : Vertex φ) :
    wireTest φ x y = true ↔ DataWire φ x y := by
  cases x with
  | inl x =>
    obtain ⟨i,a⟩ := x
    cases y with
    | inl y => simp [wireTest,DataWire]
    | inr y =>
      cases y with
      | var v => simp [wireTest,DataWire,and_assoc]
      | rail v b j => simp [wireTest,DataWire,and_assoc]
      | clause c =>
        cases h : lookup φ i with
        | none => simp [wireTest,DataWire,h]
        | some z => obtain ⟨j,l⟩ := z; simp [wireTest,DataWire,h]
  | inr x =>
    cases y with
    | inl y =>
      obtain ⟨i,a⟩ := y
      cases x with
      | var v => simp [wireTest,DataWire]
      | rail v b j => simp [wireTest,DataWire,and_assoc]
      | clause c =>
        cases h : lookup φ i with
        | none => simp [wireTest,DataWire,h]
        | some z => obtain ⟨j,l⟩ := z; simp [wireTest,DataWire,h]
    | inr y =>
      cases x <;> cases y <;> try simp [wireTest,DataWire,and_assoc]

instance wireDecidable (φ : CNF) : DecidableRel (DataWire φ) := fun x y =>
  decidable_of_iff (wireTest φ x y = true) (wireTest_correct φ x y)

instance adjacencyDecidable (φ : CNF) : DecidableRel (adjacency φ) := by
  intro x y
  cases x <;> cases y <;> unfold adjacency Edge <;> infer_instance

def vertices (φ : CNF) : List (Vertex φ) :=
  (List.finRange (levels φ)).flatMap (fun i => (List.finRange 20).map (sw i)) ++
  (List.finRange (varCount φ+1)).map (fun v => .inr (.var v)) ++
  (List.finRange (varCount φ)).flatMap (fun v =>
    [false,true].flatMap (fun b => (List.finRange (levels φ+1)).map
      (fun j => .inr (.rail v b j)))) ++
  (List.finRange (φ.length+1)).map (fun c => .inr (.clause c))

theorem mem_vertices (φ : CNF) (x : Vertex φ) : x ∈ vertices φ := by
  cases x with
  | inl z => obtain ⟨i,a⟩ := z; simp [vertices,sw]
  | inr x =>
    cases x with
    | var v => simp [vertices]
    | rail v b j => cases b <;> simp [vertices]
    | clause c => simp [vertices]

/-- Polynomial-size pair filtering; no search over subsets or paths. -/
def arcs (φ : CNF) : List (Vertex φ × Vertex φ) :=
  ((vertices φ).product (vertices φ)).filter (fun e => decide (adjacency φ e.1 e.2))

theorem mem_arcs (φ : CNF) (x y : Vertex φ) :
    (x,y) ∈ arcs φ ↔ adjacency φ x y := by
  simp [arcs,mem_vertices]

theorem arcs_length (φ : CNF) : (arcs φ).length ≤ (vertices φ).length ^ 2 := by
  have h := List.length_filter_le (fun e : Vertex φ × Vertex φ => decide (adjacency φ e.1 e.2))
    ((vertices φ).product (vertices φ))
  calc
    (arcs φ).length ≤ ((vertices φ).product (vertices φ)).length := h
    _ = (vertices φ).length ^ 2 := (List.length_product _ _).trans (pow_two _).symm

theorem vertices_length (φ : CNF) :
    (vertices φ).length = 20 * levels φ + 2 * varCount φ * (levels φ+1) +
      varCount φ + φ.length + 2 := by
  simp [vertices,List.length_flatMap]
  ring

theorem occurrence_count (φ : CNF) :
    (FormulaWiring.occurrences φ).length = SATInputBounds.occurrences φ := by
  have h : (FormulaWiring.occurrences φ).length = φ.flatten.length := by
    simp only [FormulaWiring.occurrences,List.length_flatMap,List.length_map,List.length_flatten]
    have he := congrArg (fun l : List Clause => (l.map List.length).sum)
      (List.zipIdx_map_fst 0 φ)
    simpa only [List.map_map,Function.comp_def] using he
  rw [h]
  clear h
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [List.flatten_cons,List.length_append,SATInputBounds.occurrences,List.foldr_cons]
    exact congrArg (c.length + ·) ih

theorem parameter_bounds (φ : CNF) :
    levels φ ≤ φ.encode.length+1 ∧ varCount φ ≤ φ.encode.length+1 ∧
      φ.length ≤ φ.encode.length := by
  have h := SATInputBounds.syntax_length_bound φ
  have hv := CNF.maxVar_le_encode_length φ
  unfold levels varCount
  rw [occurrence_count]
  omega

theorem vertices_polynomial (φ : CNF) :
    (vertices φ).length ≤ 30*(φ.encode.length+1)^2 := by
  obtain ⟨hn,hk,hm⟩ := parameter_bounds φ
  have hprod := Nat.mul_le_mul hk (Nat.add_le_add_right hn 1)
  rw [vertices_length]
  nlinarith

theorem arcs_polynomial (φ : CNF) :
    (arcs φ).length ≤ 900*(φ.encode.length+1)^4 := by
  have hv := vertices_polynomial φ
  have hs := Nat.mul_le_mul hv hv
  have ha := arcs_length φ
  nlinarith [sq_nonneg ((vertices φ).length : Int)]

end UnconstrainedPACDetection.FormulaEnumeration

module

public import proofs.UnconstrainedPACDetection.MixedMinor
public import Mathlib.Tactic

@[expose] public section

namespace UnconstrainedPACDetection.DirectedLinkageSource

/-- A normalized directed graph: tails may be either source or internal;
heads may be either sink or internal. The Boolean distinguishes the two terminals. -/
structure Network (V E : Type*) where
  tail : E → Bool ⊕ V
  head : E → Bool ⊕ V
  noLoop : ∀ e v, tail e = Sum.inr v → head e ≠ Sum.inr v

def tailRow {V : Type*} : Bool ⊕ V → Bool ⊕ V
  | Sum.inl _ => Sum.inl false
  | Sum.inr v => Sum.inr v

def headRow {V : Type*} : Bool ⊕ V → Bool ⊕ V
  | Sum.inl _ => Sum.inl true
  | Sum.inr v => Sum.inr v

def tailSign {V : Type*} : Bool ⊕ V → ℤ
  | Sum.inl true => 1
  | _ => -1

def headSign {V : Type*} : Bool ⊕ V → ℤ
  | Sum.inl false => -1
  | _ => 1

def factor {V : Type*} : Bool ⊕ V → ℤ
  | Sum.inl true => 2
  | _ => 1

theorem rows_distinct {V E : Type*} (D : Network V E) (e : E) :
    tailRow (D.tail e) ≠ headRow (D.head e) := by
  cases ht : D.tail e with
  | inl b => cases hh : D.head e <;> simp [tailRow, headRow]
  | inr v =>
    cases hh : D.head e with
    | inl b => simp [tailRow, headRow]
    | inr w =>
      intro h
      have hvw : v = w := Sum.inr.inj h
      subst w
      exact D.noLoop e v ht hh

theorem tailSign_ne_zero {V : Type*} (x : Bool ⊕ V) : tailSign x ≠ 0 := by
  cases x with
  | inl b => cases b <;> norm_num [tailSign]
  | inr v => norm_num [tailSign]

theorem head_coefficient_ne_zero {V : Type*} (x y : Bool ⊕ V) :
    headSign y * factor x * factor y ≠ 0 := by
  have hf : ∀ z : Bool ⊕ V, factor z ≠ 0 := by
    intro z
    cases z with
    | inl b => cases b <;> norm_num [factor]
    | inr v => norm_num [factor]
  have hs : headSign y ≠ 0 := by
    cases y with
    | inl b => cases b <;> norm_num [headSign]
    | inr v => norm_num [headSign]
  exact mul_ne_zero (mul_ne_zero hs (hf x)) (hf y)

def matrix {V E : Type*} [DecidableEq V] (D : Network V E)
    (r : Bool ⊕ V) (e : E) : ℤ :=
  if r = tailRow (D.tail e) then tailSign (D.tail e)
  else if r = headRow (D.head e) then
    headSign (D.head e) * factor (D.tail e) * factor (D.head e)
  else 0

theorem matrix_tail {V E : Type*} [DecidableEq V] (D : Network V E) (e : E) :
    matrix D (tailRow (D.tail e)) e = tailSign (D.tail e) := by
  simp [matrix]

theorem matrix_head {V E : Type*} [DecidableEq V] (D : Network V E) (e : E) :
    matrix D (headRow (D.head e)) e =
      headSign (D.head e) * factor (D.tail e) * factor (D.head e) := by
  simp [matrix, (rows_distinct D e).symm]

theorem matrix_ne_zero_iff {V E : Type*} [DecidableEq V]
    (D : Network V E) (r : Bool ⊕ V) (e : E) :
    matrix D r e ≠ 0 ↔ r = tailRow (D.tail e) ∨ r = headRow (D.head e) := by
  by_cases ht : r = tailRow (D.tail e)
  · subst r
    simp [matrix_tail, tailSign_ne_zero]
  · by_cases hh : r = headRow (D.head e)
    · subst r
      rw [matrix_head]
      exact iff_of_true (head_coefficient_ne_zero _ _) (Or.inr rfl)
    · simp [matrix, ht, hh]

theorem matrix_abs_le_four {V E : Type*} [DecidableEq V]
    (D : Network V E) (r : Bool ⊕ V) (e : E) : |matrix D r e| ≤ 4 := by
  have hf (z : Bool ⊕ V) : factor z = 1 ∨ factor z = 2 := by
    cases z with
    | inl b => cases b <;> simp [factor]
    | inr v => simp [factor]
  have hs (z : Bool ⊕ V) : headSign z = 1 ∨ headSign z = -1 := by
    cases z with
    | inl b => cases b <;> simp [headSign]
    | inr v => simp [headSign]
  have ht (z : Bool ⊕ V) : tailSign z = 1 ∨ tailSign z = -1 := by
    cases z with
    | inl b => cases b <;> simp [tailSign]
    | inr v => simp [tailSign]
  unfold matrix
  split_ifs
  · rcases ht (D.tail e) with h | h <;> rw [h] <;> norm_num
  · rcases hs (D.head e) with h | h <;>
      rcases hf (D.tail e) with h' | h' <;>
      rcases hf (D.head e) with h'' | h'' <;> rw [h, h', h''] <;> norm_num
  · norm_num

theorem column_support {V E : Type*} [Fintype V] [DecidableEq V]
    (D : Network V E) (e : E) :
    Finset.univ.filter (fun r => matrix D r e ≠ 0) =
      {tailRow (D.tail e), headRow (D.head e)} := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  exact matrix_ne_zero_iff D r e

theorem column_degree_two {V E : Type*} [Fintype V] [DecidableEq V]
    (D : Network V E) (e : E) :
    (Finset.univ.filter (fun r => matrix D r e ≠ 0)).card = 2 := by
  rw [column_support]
  simp [rows_distinct D e]

def source {V E : Type*} [DecidableEq V] (D : Network V E) :
    ReversibleSource E (Bool ⊕ V) := integerMatrixSource (matrix D)

theorem source_nonambiguous {V E : Type*} [DecidableEq V] (D : Network V E) :
    (source D).Nonambiguous := integerMatrixSource_nonambiguous (matrix D)

theorem source_net {V E : Type*} [DecidableEq V] (D : Network V E)
    (r : Bool ⊕ V) (e : E) : (source D).net r e = (matrix D r e : ℝ) :=
  integerMatrixSource_net (matrix D) r e

end UnconstrainedPACDetection.DirectedLinkageSource

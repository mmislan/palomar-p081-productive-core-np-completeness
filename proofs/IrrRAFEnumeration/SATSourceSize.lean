module

public import proofs.IrrRAFEnumeration.SATSource

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open CircuitSource SATCompletion

theorem needs_card_le {n m : Nat} (s : Step n m) : (needs s).card ≤ n + m + 2 := by
  cases s with
  | conflict i => simp [needs]
  | coverage x => simp [needs]
  | clause j x => simp [needs]
  | finish =>
      have h := Finset.card_union_le
        ((Finset.univ : Finset (Fin n)).image (Wire.covered (m := m)))
        ((Finset.univ : Finset (Fin m)).image (Wire.clause (n := n)))
      have ha := Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))
        (f := Wire.covered (m := m))
      have hb := Finset.card_image_le (s := (Finset.univ : Finset (Fin m)))
        (f := Wire.clause (n := n))
      simp only [Finset.card_univ, Fintype.card_fin] at ha hb
      dsimp [needs]
      omega

theorem produces_card_le {n m : Nat} (Φ : Fin m → Finset (Choice n)) (s : Step n m) :
    (produces Φ s).card ≤ 1 := by
  cases s with
  | conflict i => simp [produces]
  | coverage x => simp [produces]
  | clause j x => by_cases h : x ∈ Φ j <;> simp [produces, h]
  | finish => simp [produces]

/-- A literal sparse-incidence budget: food, molecule and reaction identifiers,
reactant rows, product rows and catalyst rows all receive explicit charges. -/
def encodingBudget (n m : Nat) : Nat :=
  let a := 2*n
  let w := 3*n + m + 1
  let q := 3*n + 2*n*m + 1
  1 + (1+w+(q+1)) + (a+q+1) + (a+q*(n+m+2)+1) + (a+2*q+1+w) + (a+q+1)

/-- Polynomial domination of the entire incidence budget. Integer identifiers
can be represented with at most this many bits each, giving a squared bound. -/
theorem encodingBudget_polynomial (n m : Nat) :
    encodingBudget n m ≤ 100 * (n + m + 1)^3 := by
  dsimp [encodingBudget]
  nlinarith [sq_nonneg (n : Int), sq_nonneg (m : Int), Nat.zero_le (n*n*m),
    Nat.zero_le (n*m*m), Nat.zero_le (n*n*n), Nat.zero_le (m*m*m)]

def moleculeEquiv (w q : Nat) : Molecule w q ≃ Unit ⊕ (Fin w ⊕ Fin (q+1)) where
  toFun
    | .food => .inl ()
    | .wire i => .inr (.inl i)
    | .marker j => .inr (.inr j)
  invFun
    | .inl _ => .food
    | .inr (.inl i) => .wire i
    | .inr (.inr j) => .marker j
  left_inv := by intro x; cases x <;> rfl
  right_inv := by rintro (u | i | j) <;> rfl

theorem molecule_card (w q : Nat) : Fintype.card (Molecule w q) = w + q + 2 := by
  have h := Fintype.card_congr (moleculeEquiv w q)
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin] at h
  omega

/-- Actual incidence count of the constructed CRS, including all catalyst
incidences. This definition does not assume a source-size bound. -/
noncomputable def literalIncidences {n m : Nat} (Φ : Fin m → Finset (Choice n)) : Nat := by
  classical
  exact
  let Q := crs (rules Φ)
  Fintype.card (Molecule (Fintype.card (Wire n m)) (Fintype.card (Step n m))) +
  Fintype.card (Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m))) +
  Q.food.card +
  (∑ r, (Q.inputs r).card) + (∑ r, (Q.outputs r).card) +
  (∑ r : Reaction (Fintype.card (Choice n)) (Fintype.card (Step n m)),
    (Finset.univ.filter (fun x => catalysis (w := Fintype.card (Wire n m)) x r)).card)

theorem literalIncidences_le_dense {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    literalIncidences Φ ≤
      let W := Fintype.card (Wire n m)
      let Q := Fintype.card (Step n m)
      let A := Fintype.card (Choice n)
      1 + (W+Q+2) + 2*(A+Q+1) + 2*(A+Q+1)*(W+Q+2) := by
  classical
  let W := Fintype.card (Wire n m)
  let Q := Fintype.card (Step n m)
  let A := Fintype.card (Choice n)
  have hi : (∑ r : Reaction A Q, ((crs (rules Φ)).inputs r).card) ≤
      Fintype.card (Reaction A Q) * Fintype.card (Molecule W Q) := by
    calc
      _ ≤ ∑ _r : Reaction A Q, Fintype.card (Molecule W Q) := by
        apply Finset.sum_le_sum
        intro r _
        exact Finset.card_le_univ _
      _ = _ := by simp
  have ho : (∑ r : Reaction A Q, ((crs (rules Φ)).outputs r).card) ≤
      Fintype.card (Reaction A Q) * Fintype.card (Molecule W Q) := by
    calc
      _ ≤ ∑ _r : Reaction A Q, Fintype.card (Molecule W Q) := by
        apply Finset.sum_le_sum
        intro r _
        exact Finset.card_le_univ _
      _ = _ := by simp
  have hc : ∀ r : Reaction A Q,
      (Finset.univ.filter (fun x => catalysis (w := W) x r)).card = 1 := by
    intro r
    unfold catalysis
    rw [Finset.filter_congr_decidable]
    rw [Finset.filter_eq']
    simp
  have hfood : (crs (rules Φ)).food.card = 1 := by simp [crs]
  unfold literalIncidences
  dsimp only
  dsimp only [W, Q, A] at hc
  simp only [hc]
  simp only [hfood, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one, molecule_card, Reaction, Fintype.card_sum, Fintype.card_fin]
  simp only [Reaction, Fintype.card_sum, Fintype.card_fin, molecule_card] at hi ho
  dsimp only [W, Q, A] at hi ho
  nlinarith

theorem literalIncidences_polynomial {n m : Nat} (Φ : Fin m → Finset (Choice n)) :
    literalIncidences Φ ≤ 300 * (n+m+1)^4 := by
  have h := literalIncidences_le_dense Φ
  dsimp only at h
  rw [wire_card, step_card] at h
  simp only [Choice, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h
  nlinarith [Nat.zero_le (n^4), Nat.zero_le (m^4), Nat.zero_le (n^3*m),
    Nat.zero_le (n*m^3), Nat.zero_le (n^2*m^2), Nat.zero_le (n^3),
    Nat.zero_le (m^3), Nat.zero_le (n^2*m), Nat.zero_le (n*m^2)]

end IrrRAFEnumeration.SATSource

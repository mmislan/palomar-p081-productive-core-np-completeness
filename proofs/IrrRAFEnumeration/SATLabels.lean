module

public import proofs.IrrRAFEnumeration.SATCompletion
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open SATCompletion

inductive Wire (n m : Nat)
  | literal (x : Choice n)
  | covered (i : Fin n)
  | clause (j : Fin m)
  | output
  deriving DecidableEq, Fintype

inductive Step (n m : Nat)
  | conflict (i : Fin n)
  | coverage (x : Choice n)
  | clause (j : Fin m) (x : Choice n)
  | finish
  deriving DecidableEq, Fintype

def wireEquiv (n m : Nat) : Wire n m ≃ Choice n ⊕ (Fin n ⊕ (Fin m ⊕ Unit)) where
  toFun
    | .literal x => .inl x
    | .covered i => .inr (.inl i)
    | .clause j => .inr (.inr (.inl j))
    | .output => .inr (.inr (.inr ()))
  invFun
    | .inl x => .literal x
    | .inr (.inl i) => .covered i
    | .inr (.inr (.inl j)) => .clause j
    | .inr (.inr (.inr _)) => .output
  left_inv := by intro x; cases x <;> rfl
  right_inv := by rintro (x | i | j | u) <;> rfl

def stepEquiv (n m : Nat) : Step n m ≃ Fin n ⊕ (Choice n ⊕ ((Fin m × Choice n) ⊕ Unit)) where
  toFun
    | .conflict i => .inl i
    | .coverage x => .inr (.inl x)
    | .clause j x => .inr (.inr (.inl (j,x)))
    | .finish => .inr (.inr (.inr ()))
  invFun
    | .inl i => .conflict i
    | .inr (.inl x) => .coverage x
    | .inr (.inr (.inl (j,x))) => .clause j x
    | .inr (.inr (.inr _)) => .finish
  left_inv := by intro x; cases x <;> rfl
  right_inv := by rintro (i | x | ⟨j,x⟩ | u) <;> rfl

theorem wire_card (n m : Nat) : Fintype.card (Wire n m) = 3*n + m + 1 := by
  have h := Fintype.card_congr (wireEquiv n m)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_unit] at h
  omega

theorem step_card (n m : Nat) : Fintype.card (Step n m) = 3*n + 2*n*m + 1 := by
  have h := Fintype.card_congr (stepEquiv n m)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_unit] at h
  nlinarith


/-- Explicit Boolean labels, with no choice-based enumeration. -/
def bitCode : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := i.val = 1
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def unitCode : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv := by intro u; cases u; rfl
  right_inv := by intro i; exact Subsingleton.elim _ _

def choiceOffset (n : Nat) : Choice n ≃ Fin (n*2) :=
  (Equiv.prodCongr (Equiv.refl (Fin n)) bitCode).trans finProdFinEquiv

def wireOffset (n m : Nat) : Wire n m ≃ Fin (n*2 + (n + (m+1))) :=
  (wireEquiv n m).trans ((Equiv.sumCongr (choiceOffset n)
    ((Equiv.sumCongr (Equiv.refl (Fin n))
      ((Equiv.sumCongr (Equiv.refl (Fin m)) unitCode).trans finSumFinEquiv)).trans
        finSumFinEquiv)).trans finSumFinEquiv)

def stepOffset (n m : Nat) : Step n m ≃ Fin (n + (n*2 + (m*(n*2)+1))) :=
  (stepEquiv n m).trans ((Equiv.sumCongr (Equiv.refl (Fin n))
    ((Equiv.sumCongr (choiceOffset n)
      ((Equiv.sumCongr
        ((Equiv.prodCongr (Equiv.refl (Fin m)) (choiceOffset n)).trans finProdFinEquiv)
        unitCode).trans finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)

/-- Cardinality casts erase at runtime; the data maps are explicit offsets. -/
def inputCode (n : Nat) : Choice n ≃ Fin (Fintype.card (Choice n)) :=
  (choiceOffset n).trans (finCongr (by simp [Choice]))

def wireCode (n m : Nat) : Wire n m ≃ Fin (Fintype.card (Wire n m)) :=
  (wireOffset n m).trans (finCongr (by rw [wire_card]; omega))

def stepCode (n m : Nat) : Step n m ≃ Fin (Fintype.card (Step n m)) :=
  (stepOffset n m).trans (finCongr (by rw [step_card]; ring))

theorem inputCode_value {n : Nat} (x : Choice n) :
    (inputCode n x).val = 2*x.1.val + (if x.2 then 1 else 0) := by
  rcases x with ⟨i, b⟩
  cases b <;> simp [inputCode, choiceOffset, bitCode, finProdFinEquiv, Nat.add_comm]

theorem wireCode_output (n m : Nat) :
    (wireCode n m .output).val = 3*n+m := by
  simp [wireCode, wireOffset, wireEquiv, unitCode, finSumFinEquiv]
  omega

theorem stepCode_finish (n m : Nat) :
    (stepCode n m .finish).val = 3*n+2*n*m := by
  simp [stepCode, stepOffset, stepEquiv, unitCode, finSumFinEquiv]
  ring

end IrrRAFEnumeration.SATSource

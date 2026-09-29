module

public import proofs.UnconstrainedPACDetection.FormulaValidWriter
public import proofs.Complexitylib.Classes.P.NormalForm

@[expose] public section

namespace UnconstrainedPACDetection.FormulaPolynomialBudget
open Complexity Complexity.TM Polynomial

def Bounded (f : SAT.CNF → Nat) : Prop := ∃ p : Polynomial Nat, ∀ φ, f φ ≤ p.eval φ.encode.length

theorem constant (c : Nat) : Bounded (fun _ => c) := ⟨C c,by simp⟩

theorem input_length : Bounded (fun φ => φ.encode.length) := ⟨X,by simp⟩

theorem add {f g : SAT.CNF → Nat} (hf : Bounded f) (hg : Bounded g) : Bounded (fun φ => f φ+g φ) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,fun φ => by simpa only [eval_add] using Nat.add_le_add (hp φ) (hq φ)⟩

theorem mul {f g : SAT.CNF → Nat} (hf : Bounded f) (hg : Bounded g) : Bounded (fun φ => f φ*g φ) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,fun φ => by simpa only [eval_mul] using Nat.mul_le_mul (hp φ) (hq φ)⟩

theorem pow {f : SAT.CNF → Nat} (k : Nat) (hf : Bounded f) : Bounded (fun φ => f φ^k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k,fun φ => by simpa only [eval_pow] using Nat.pow_le_pow_left (hp φ) k⟩

theorem sub {f : SAT.CNF → Nat} (g : SAT.CNF → Nat) (hf : Bounded f) : Bounded (fun φ => f φ-g φ) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun φ => (Nat.sub_le _ _).trans (hp φ)⟩

theorem mono {f g : SAT.CNF → Nat} (hg : Bounded g) (h : ∀ φ, f φ≤g φ) : Bounded f := by
  obtain ⟨p,hp⟩ := hg
  exact ⟨p,fun φ => (h φ).trans (hp φ)⟩

theorem levels : Bounded FormulaWiring.levels :=
  mono (add input_length (constant 1)) (fun φ => (FormulaEnumeration.parameter_bounds φ).1)

theorem variable_count : Bounded FormulaWiring.varCount :=
  mono (add input_length (constant 1)) (fun φ => (FormulaEnumeration.parameter_bounds φ).2.1)

theorem clauses : Bounded (fun φ => φ.length) :=
  mono input_length (fun φ => (FormulaEnumeration.parameter_bounds φ).2.2)

theorem labels : Bounded (fun φ => (FormulaIndexedGraph.labels φ).length) :=
  mono (mul (constant 30) (pow 2 (add input_length (constant 1)))) FormulaIndexedGraph.labels_bound

theorem header_clauses : Bounded (fun φ => FormulaHeaders.clauses φ.encode) :=
  mono (add input_length (constant 1)) (fun φ => (FormulaHeaders.parameter_bounds φ.encode).1)

theorem header_occurrences : Bounded (fun φ => FormulaHeaderPreparation.occurrences φ.encode) :=
  mono (add input_length (constant 1)) (fun φ => (FormulaHeaders.parameter_bounds φ.encode).2.1)

theorem header_maximum : Bounded (fun φ => FormulaHeaderPreparation.maximum φ.encode+1) :=
  mono (add (mul (constant 3) input_length) (constant 2)) (fun φ => (FormulaHeaders.parameter_bounds φ.encode).2.2)

theorem header_entity : Bounded (fun φ => FormulaEntityHeader.value φ.encode) := by
  apply mono (mul (constant 128) (pow 2 (add input_length (constant 1))))
  intro φ
  exact FormulaHeaderRegisters.value_bound φ.encode.length _ _
    (FormulaHeaders.parameter_bounds φ.encode).2.1 (FormulaHeaders.parameter_bounds φ.encode).2.2

theorem header_reaction : Bounded (fun φ => FormulaHeaders.value φ.encode) := by
  apply mono (mul (constant 128) (pow 2 (add input_length (constant 1))))
  intro φ
  exact FormulaReactionRegisters.value_bound φ.encode.length _ _ _
    (FormulaHeaders.parameter_bounds φ.encode).1 (FormulaHeaders.parameter_bounds φ.encode).2.1
    (FormulaHeaders.parameter_bounds φ.encode).2.2

theorem reaction_bits : Bounded (fun φ => (FormulaHeaders.value φ.encode).bits.length) := by
  apply mono (add header_reaction (constant 1))
  intro φ
  have h := VerifierUnaryBinary.digits_length (FormulaHeaders.value φ.encode)
  rw [FormulaHeaderBinaryDigits.digits_eq_bits] at h
  exact h

end UnconstrainedPACDetection.FormulaPolynomialBudget

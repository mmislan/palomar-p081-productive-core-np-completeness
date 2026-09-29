module

public import proofs.UnconstrainedPACDetection.FormulaIndexedGraph
public import proofs.UnconstrainedPACDetection.FiniteMarkedSource
public import proofs.UnconstrainedPACDetection.BinaryPACVerifier
public import proofs.Complexitylib.SAT.Language
public import proofs.Complexitylib.SAT.Verifier

@[expose] public section

namespace UnconstrainedPACDetection.FormulaPACEncoding
open Complexity.SAT

def table (φ : CNF) : BinarySourceData.DenseSource :=
  FiniteMarkedSource.dense (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ)

def encode (φ : CNF) : List Bool := (table φ).encode

theorem decode_encode (φ : CNF) : BinarySourceData.decode (encode φ) = some (table φ) :=
  FiniteMarkedSource.decode_dense _ _

theorem table_pac_iff_sat (φ : CNF) :
    (∃ c, (table φ).toSource.PAC c) ↔ φ.Satisfiable :=
  (FiniteMarkedSource.dense_pac_iff _ _).trans (FormulaIndexedGraph.linkage_iff_sat φ)

/-- The executable output bits belong to the actual PAC language exactly on SAT inputs. -/
theorem encode_mem_iff_sat (φ : CNF) :
    encode φ ∈ BinaryPACVerifier.language ↔ φ.Satisfiable := by
  simp only [BinaryPACVerifier.language,Set.mem_ofPred_eq,decode_encode,
    Option.some.injEq]
  constructor
  · rintro ⟨s,he,hp⟩
    subst s
    exact (table_pac_iff_sat φ).mp hp
  · intro h
    exact ⟨table φ,rfl,(table_pac_iff_sat φ).mpr h⟩

/-- Total bitstring map. Malformed SAT syntax is sent to a fixed NO instance. -/
def compile (input : List Bool) : List Bool :=
  match CNF.decode? input with
  | none => encode [[]]
  | some φ => encode φ

/-- Correctness of the total executable bitstring map; FP execution remains separate. -/
theorem compile_correct (input : List Bool) :
    compile input ∈ BinaryPACVerifier.language ↔ input ∈ Complexity.SAT.language := by
  cases hd : CNF.decode? input with
  | none =>
    have hnot : input ∉ Complexity.SAT.language := by
      rintro ⟨φ,rfl,_⟩
      simp at hd
    have hn : ¬CNF.Satisfiable ([[]] : CNF) := by
      simp [CNF.Satisfiable,CNF.eval,Clause.eval]
    simp [compile,hd,encode_mem_iff_sat,hn,hnot]
  | some φ =>
    have he := CNF.decode?_sound hd
    subst input
    simp only [compile,CNF.decode?_encode,encode_mem_iff_sat]
    constructor
    · intro h
      exact ⟨φ,rfl,h⟩
    · rintro ⟨ψ,he,hψ⟩
      have h := congrArg CNF.decode? he
      simp only [CNF.decode?_encode,Option.some.injEq] at h
      subst ψ
      exact hψ

end UnconstrainedPACDetection.FormulaPACEncoding

module

public import proofs.UnconstrainedPACDetection.FormulaRows

@[expose] public section

namespace UnconstrainedPACDetection.FormulaSides
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def machine : TM 28 := seqTM (FormulaRows.machine false) (FormulaRows.machine true)

def budget (φ : SAT.CNF) : Nat := 2*FormulaRows.budget φ+1

theorem hoare (φ : SAT.CNF) (ys : List Bool) : machine.HoareTime
    (EmitPred (word φ.encode) (FormulaRows.frame φ) ys)
    (EmitPred (word φ.encode) (FormulaRows.frame φ)
      (ys ++ FormulaOrderedSchedule.bits (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ)))
    (budget φ) := by
  have h0 := FormulaRows.canonical_hoare φ false ys
  have h1 := FormulaRows.canonical_hoare φ true (ys ++ FormulaRows.bits φ false)
  have h := seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) (FormulaRows.parked φ) _) h1
  have he : FormulaRows.bits φ false ++ FormulaRows.bits φ true =
      FormulaOrderedSchedule.bits (FormulaIndexedGraph.edge φ) (FormulaIndexedGraph.terminals φ) := by
    rw [FormulaRows.scan_bits,FormulaRows.scan_bits]
    exact (List.flatMap_append).symm
  rw [List.append_assoc,he] at h
  exact h.mono_bound (by unfold budget; omega)

theorem canonical_hoare (φ : SAT.CNF) : machine.HoareTime
    (EmitPred (word φ.encode) (FormulaRows.frame φ)
      (BinaryFields.encodeField (FormulaPACEncoding.table φ).entities.bits ++
        BinaryFields.encodeField (FormulaPACEncoding.table φ).reactions.bits))
    (EmitPred (word φ.encode) (FormulaRows.frame φ) (FormulaPACEncoding.encode φ)) (budget φ) := by
  have h := hoare φ (BinaryFields.encodeField (FormulaPACEncoding.table φ).entities.bits ++
    BinaryFields.encodeField (FormulaPACEncoding.table φ).reactions.bits)
  rw [← FormulaOrderedSchedule.formula_encode] at h
  exact h

end UnconstrainedPACDetection.FormulaSides

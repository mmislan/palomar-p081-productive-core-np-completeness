module

public import proofs.UnconstrainedPACDetection.FormulaHeaderBridge

@[expose] public section

namespace UnconstrainedPACDetection.FormulaValidWriter
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked)

def machine : TM 28 := seqTM FormulaHeaderFrame.machine (seqTM FormulaHeaderBridge.machine FormulaSides.machine)

def budget (φ : SAT.CNF) : Nat := FormulaHeaders.bound φ.encode+FormulaHeaderBridge.budget φ.encode+FormulaSides.budget φ+2

theorem hoare (φ : SAT.CNF) : machine.HoareTime (FormulaHeaderFrame.initial φ.encode)
    (EmitPred (word φ.encode) (FormulaRows.frame φ) (FormulaPACEncoding.encode φ)) (budget φ) := by
  have h0 := FormulaHeaderFrame.hoare φ.encode
  have h1 := FormulaHeaderBridge.hoare φ (FormulaHeaders.fields φ.encode)
  have h2 := FormulaSides.canonical_hoare φ
  obtain ⟨he,hr⟩ := FormulaHeaders.decoded_values φ
  have hf : FormulaHeaders.fields φ.encode = BinaryFields.encodeField (FormulaPACEncoding.table φ).entities.bits ++
      BinaryFields.encodeField (FormulaPACEncoding.table φ).reactions.bits := by
    simp only [FormulaHeaders.fields,he,hr]
  rw [← hf] at h2
  have h12 := seqTM_hoareTime _ _ h1 (emitPred_transition (word_parked _) (FormulaRows.parked φ) _) h2
  have h := seqTM_hoareTime _ _ h0 (emitPred_transition (word_parked _) (FormulaHeaderFrame.parked _) _) h12
  exact h.mono_bound (by unfold budget; omega)

end UnconstrainedPACDetection.FormulaValidWriter

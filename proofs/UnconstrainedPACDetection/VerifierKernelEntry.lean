module

public import proofs.UnconstrainedPACDetection.VerifierKernelRegisters
public import proofs.UnconstrainedPACDetection.VerifierRawFrame

@[expose] public section

namespace UnconstrainedPACDetection.VerifierKernelEntry
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)

def target (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) : Fin 18 → Tape :=
  VerifierPreparedLayout.join (VerifierPreparedCertificate.frame s w 2)
    (VerifierActivationProduce.frame s w (wordTape []))

theorem target_slots (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) :
    target s w = ![regTape 0,regTape 1,regTape 0,regTape 0,wordTape w.encode,
      regTape 0,regTape 0,regTape 0,regTape 0,regTape (s.entities-1),
      regTape (s.reactions-1),regTape 0,regTape 2,regTape s.entities,
      wordTape w.encode,regTape 0,regTape (2*s.reactions),regTape 0] := by
  funext j
  fin_cases j
  all_goals first | rfl | exact VerifierCountPrepare.unary_eq_reg 0 | exact VerifierCountPrepare.unary_eq_reg _

def finalWork (work : Fin 30 → Tape) (s : BinarySourceData.DenseSource)
    (w : BinaryWitnessData.Witness) :=
  VerifierKernelRegisters.finalWork (VerifierWitnessPlacement.placed work w.encode)
    s.entities s.reactions

theorem final_prefix (work : Fin 30 → Tape) (s : BinarySourceData.DenseSource)
    (w : BinaryWitnessData.Witness)
    (hz : ∀ j : Fin 30, j.val < 18 → work j = regTape 0) :
    ∀ j : Fin 18, finalWork work s w (placeWorkIdx 0 12 j) = target s w j := by
  intro j
  rw [target_slots]
  fin_cases j
  all_goals simp [finalWork,VerifierKernelRegisters.finalWork,VerifierWitnessPlacement.placed,
    VerifierWitnessPlacement.restored,placeWorkIdx]
  all_goals exact hz _ (by decide)

def machine : TM 30 := seqTM VerifierWitnessPlacement.machine VerifierKernelRegisters.machine

/-- Complete witness and register initialization for the exact prepared consumer.
The remaining raw-validation docking must supply these measured registers,
original witness cells and a charged cursor bound. -/
theorem entry_hoare (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (inp : Tape) (work : Fin 30 → Tape) (B : Nat)
    (hi : Parked inp) (hw : ∀ j, Parked (work j))
    (hc : (work 27).cells = (wordTape w.encode).cells) (hb : (work 27).head ≤ B)
    (hm : work 23 = regTape s.entities) (hn : work 26 = regTape s.reactions)
    (hz : ∀ j : Fin 30, j.val < 18 → work j = regTape 0) :
    machine.HoareTime (EmitPred inp work []) (EmitPred inp (finalWork work s w) [])
      (B+6*w.encode.length+23+100*(s.entities+s.reactions+1)^2) := by
  let W := VerifierWitnessPlacement.placed work w.encode
  have hp : ∀ j, Parked (W j) :=
    VerifierWitnessPlacement.updated_parked _ 14 _
      (VerifierWitnessPlacement.updated_parked _ 4 _
        (VerifierWitnessPlacement.updated_parked _ 27 _ hw))
  have ha := VerifierWitnessPlacement.placement_hoare w.encode inp work B hi hw hc hb
    (hz 4 (by decide)) (hz 14 (by decide))
  have hb' := VerifierKernelRegisters.registers_hoare s.entities s.reactions inp W hi hp
    (by simpa [W,VerifierWitnessPlacement.placed,VerifierWitnessPlacement.restored] using hm)
    (by simpa [W,VerifierWitnessPlacement.placed,VerifierWitnessPlacement.restored] using hn) (by
      intro j hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simpa [W,VerifierWitnessPlacement.placed,VerifierWitnessPlacement.restored]
        using hz _ (by decide))
  have h := seqTM_hoareTime _ _ ha (emitPred_transition hi hp []) hb'
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierKernelEntry

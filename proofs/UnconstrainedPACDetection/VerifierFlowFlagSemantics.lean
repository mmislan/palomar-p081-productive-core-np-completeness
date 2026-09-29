module

public import proofs.UnconstrainedPACDetection.VerifierFlowFlagPass

@[expose] public section

namespace UnconstrainedPACDetection.VerifierFlowFlagSemantics
open VerifierActivationSemantics (verdict)
open VerifierFlowFlagPass (accept)

def pairs (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (side : Bool) : List (ℤ × Bool) :=
  (List.finRange s.reactions).map (fun r => (w.values s.reactions r,verdict s w side r))

theorem flows (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (side : Bool) :
    (pairs s w side).map Prod.fst = w.flow := by
  apply List.ext_getElem
  · simp [pairs,hw]
  · intro i hi hj
    simp only [pairs,List.length_map,List.length_finRange] at hi
    simp [pairs,BinaryWitnessData.Witness.values,List.getD,show i < w.flow.length by omega]

theorem flags (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (side : Bool) :
    (pairs s w side).map Prod.snd = (List.finRange s.reactions).map (verdict s w side) := by
  simp [pairs,List.map_map,Function.comp_def]

theorem all_flags (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) :
    VerifierActivationSource.flags s w = (pairs s w false).map Prod.snd ++ (pairs s w true).map Prod.snd := by
  rw [flags,flags]; rfl

theorem accept_iff (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (side a : Bool) :
    accept (pairs s w side) a = true ↔
      a = true ∧ ∀ r : Fin s.reactions, w.values s.reactions r ≠ 0 → verdict s w side r = true := by
  rw [VerifierFlowFlagPass.accept_iff]
  simp [pairs]

theorem both_iff (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) :
    accept (pairs s w true) (accept (pairs s w false) true) = true ↔
      ∀ r, w.values s.reactions r ≠ 0 → s.toSource.sideAdmissible (w.entities s.entities) r := by
  rw [accept_iff,accept_iff]
  simp only [true_and]
  simp_rw [VerifierActivationSemantics.sideAdmissible_iff]
  constructor
  · rintro ⟨hl,hr⟩ r h; exact ⟨hl r h,hr r h⟩
  · intro h; exact ⟨fun r hr => (h r hr).1,fun r hr => (h r hr).2⟩

theorem integerFlowChecks_iff (s : BinarySourceData.DenseSource) (hn : 0 < s.reactions)
    (w : BinaryWitnessData.Witness) :
    s.toSource.IntegerFlowChecks (w.entities s.entities) (w.values s.reactions) ↔
      (w.entities s.entities).Nonempty ∧
      accept (pairs s w true) (accept (pairs s w false) true) = true ∧
      VerifierEntityOuterLoop.accumulator s hn w true s.entities = true := by
  rw [VerifierEntityOuterSemantics.integerFlowChecks_iff,both_iff]

end UnconstrainedPACDetection.VerifierFlowFlagSemantics

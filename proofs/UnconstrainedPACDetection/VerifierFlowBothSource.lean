module

public import proofs.UnconstrainedPACDetection.VerifierFlowBoth

@[expose] public section

namespace UnconstrainedPACDetection.VerifierFlowBothSource
open Complexity Complexity.TM
open VerifierFlowPassHoare (wire advance ended)
open VerifierFlowRestart (flowInput)
open VerifierMaskRestore (fixed)
open VerifierFlowFlagPass (accept)
open VerifierFlowFlagSemantics (pairs)
open VerifierActivationScan (flag)
open VerifierVerdictAnd (one)
open VerifierBufferedProduct (wordTape)

def flowWire (w : BinaryWitnessData.Witness) : List Bool :=
  BinaryFields.encode (w.flow.map BinaryFields.writeInt)

def result (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) : Bool :=
  accept (pairs s w true) (accept (pairs s w false) true)

theorem pair_wire (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) (side : Bool) : wire (pairs s w side) = flowWire w := by
  unfold wire flowWire
  have he := congrArg (List.map BinaryFields.writeInt) (VerifierFlowFlagSemantics.flows s w hw side)
  simpa only [List.map_map,Function.comp_def] using congrArg BinaryFields.encode he

theorem loop_hoare (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) :
    VerifierFlowBoth.machine.HoareTime
      (fixed (flowInput w.mask (flowWire w)) (wordTape (VerifierActivationSource.flags s w)) (flag .start true))
      (fixed (ended w.encode) (advance (wordTape (VerifierActivationSource.flags s w)) (2*s.reactions))
        (one .start (result s w))) (5*w.encode.length+10) := by
  have h := VerifierFlowBoth.both_hoare (pairs s w false) (pairs s w true) w.mask []
    (wordTape (VerifierActivationSource.flags s w)) .start true
    (by rw [pair_wire s w hw,pair_wire s w hw]) (by
      rw [List.append_nil,← VerifierFlowFlagSemantics.all_flags]
      exact (Tape.init_move_right_hasBinaryString _).hasBinarySuffix)
  rw [pair_wire s w hw] at h
  have hb : 3*(flowWire w).length+4*w.mask.length+(pairs s w false).length+(pairs s w true).length+10 ≤
      5*w.encode.length+10 := by
    have hc := BinaryWireBounds.field_count_le (w.flow.map BinaryFields.writeInt)
    simp only [List.length_map] at hc
    change w.flow.length ≤ (flowWire w).length at hc
    have he : w.encode.length = 2*w.mask.length+1+(flowWire w).length := by
      change (BinaryFields.encodeField w.mask ++ flowWire w).length = _
      simp [BinaryFields.encodeField_length]
    simp only [pairs,List.length_map,List.length_finRange]
    omega
  have hh := h.mono_bound hb
  have hadv : advance (advance (wordTape (VerifierActivationSource.flags s w)) (pairs s w false).length)
      (pairs s w true).length = advance (wordTape (VerifierActivationSource.flags s w)) (2*s.reactions) := by
    apply Tape.ext
    · simp [advance,pairs]; omega
    · rfl
  simpa only [hadv,result,BinaryWitnessData.Witness.encode,BinaryFields.encode,List.flatMap_cons,flowWire] using hh

theorem result_iff (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) :
    result s w = true ↔
      ∀ r, w.values s.reactions r ≠ 0 → s.toSource.sideAdmissible (w.entities s.entities) r :=
  VerifierFlowFlagSemantics.both_iff s w

end UnconstrainedPACDetection.VerifierFlowBothSource

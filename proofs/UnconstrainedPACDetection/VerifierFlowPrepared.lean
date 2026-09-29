module

public import proofs.UnconstrainedPACDetection.VerifierFlowBothSource

@[expose] public section

namespace UnconstrainedPACDetection.VerifierFlowPrepared
open Complexity Complexity.TM
open VerifierMaskRestore (fixed)
open VerifierBufferedProduct (wordTape)
open VerifierVerdictAnd (one)
open VerifierFlowBothSource (flowWire result)
open VerifierFlowPassHoare (advance ended)

def machine : TM 1 := seqTM VerifierFlowRestart.skip VerifierFlowBoth.machine

theorem check_hoare (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness)
    (hw : w.flow.length = s.reactions) :
    machine.HoareTime
      (fixed (wordTape w.encode) (wordTape (VerifierActivationSource.flags s w)) (one .start true))
      (fixed (ended w.encode) (advance (wordTape (VerifierActivationSource.flags s w)) (2*s.reactions))
        (one .start (result s w))) (6*w.encode.length+12) := by
  let wt := wordTape (VerifierActivationSource.flags s w)
  have hwt : wt.read ≠ .start := (Tape.init_move_right_hasBinaryString _).hasBinarySuffix.read_ne_start
  have hf : (VerifierActivationScan.flag .start true).read ≠ .start := by change Γ.one ≠ Γ.start; decide
  have first := VerifierFlowRestart.skip_hoare w.mask (flowWire w) wt hwt .start true
  have h := seqTM_hoareTime _ _ first
    (VerifierFlowPassHoare.fixed_stable _ wt _
      (VerifierFlowRestart.flowInput_suffix w.mask (flowWire w)).read_ne_start hwt hf)
    (VerifierFlowBothSource.loop_hoare s w hw)
  have hm : 2*w.mask.length+1 ≤ w.encode.length := by
    change 2*w.mask.length+1 ≤ (BinaryFields.encodeField w.mask ++ flowWire w).length
    simp only [List.length_append,BinaryFields.encodeField_length]; omega
  exact h.mono_bound (by omega)

end UnconstrainedPACDetection.VerifierFlowPrepared

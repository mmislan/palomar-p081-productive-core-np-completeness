module

public import proofs.UnconstrainedPACDetection.VerifierActivationAlignment
public import proofs.UnconstrainedPACDetection.BinaryWireBounds

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationSource
open Complexity Complexity.TM
open VerifierActivationAlignment (rows)
open VerifierActivationSemantics (verdict)
open VerifierActivationBody (pred)
open VerifierBufferedProduct (wordTape)

def flags (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) : List Bool :=
  (List.finRange s.reactions).map (verdict s w false) ++
    (List.finRange s.reactions).map (verdict s w true)

theorem rows_flags (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) :
    (rows s w).map (fun es => VerifierActivationSide.hit es false) = flags s w := by
  simp only [rows,flags,List.map_append,List.map_map]
  rfl

theorem wire_le (s : BinarySourceData.DenseSource) (hs : s.WellFormed) (w : BinaryWitnessData.Witness) :
    VerifierActivationBudget.wire (rows s w) ≤ s.encode.length := by
  rw [VerifierActivationBudget.wire,VerifierActivationAlignment.fields s hs w]
  change (BinaryFields.encode (s.values.map Nat.bits)).length ≤
    (BinaryFields.encodeField s.entities.bits ++
      (BinaryFields.encodeField s.reactions.bits ++ BinaryFields.encode (s.values.map Nat.bits))).length
  simp only [List.length_append]; omega

theorem loop_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (w : BinaryWitnessData.Witness) (hm : w.mask.length = s.entities) (initial : List Bool) :
    VerifierActivationLoop.machine.HoareTime
      (pred (BinaryFields.encode (s.values.map Nat.bits)) (wordTape w.encode)
        (regTape (2*s.reactions)) initial)
      (pred [] (wordTape w.encode) (regTape (2*s.reactions)) (initial ++ flags s w))
      (20*(s.encode.length+2*s.reactions+1)^2) := by
  have h := VerifierActivationBudget.loop_hoare (rows s w) [] w.mask
    (BinaryFields.encode (w.flow.map BinaryFields.writeInt)) initial
    (VerifierActivationAlignment.rows_mask s w hm)
  have hbound : 20*(VerifierActivationBudget.wire (rows s w)+(rows s w).length+1)^2 ≤
      20*(s.encode.length+2*s.reactions+1)^2 := by
    rw [VerifierActivationAlignment.rows_length]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by have := wire_le s hs w; omega) 2)
  have hh := h.mono_bound hbound
  simpa only [VerifierActivationLoop.suffix,List.drop_zero,
    VerifierActivationAlignment.fields s hs w,List.append_nil,
    VerifierActivationAlignment.rows_length,rows_flags,BinaryWitnessData.Witness.encode,
    BinaryFields.encode,List.flatMap_cons] using hh

theorem left_flag (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (r : Fin s.reactions) :
    (flags s w).getD r.val false = verdict s w false r := by
  rw [List.getD_eq_getElem _ _ (by simp [flags]; omega)]
  simp [flags,r.isLt]

theorem right_flag (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) (r : Fin s.reactions) :
    (flags s w).getD (s.reactions+r.val) false = verdict s w true r := by
  rw [List.getD_eq_getElem _ _ (by simp [flags])]
  simp [flags]

theorem wire_hoare (s : BinarySourceData.DenseSource) (hs : s.WellFormed)
    (w : BinaryWitnessData.Witness) (hm : w.mask.length = s.entities)
    (hw : w.flow.length = s.reactions) (initial : List Bool) :
    VerifierActivationLoop.machine.HoareTime
      (pred (BinaryFields.encode (s.values.map Nat.bits)) (wordTape w.encode)
        (regTape (2*s.reactions)) initial)
      (pred [] (wordTape w.encode) (regTape (2*s.reactions)) (initial ++ flags s w))
      (20*(s.encode.length+2*w.encode.length+1)^2) := by
  have hc := BinaryWireBounds.field_count_le (w.mask :: w.flow.map BinaryFields.writeInt)
  simp only [List.length_cons,List.length_map] at hc
  change w.flow.length+1 ≤ w.encode.length at hc
  have hb : 20*(s.encode.length+2*s.reactions+1)^2 ≤ 20*(s.encode.length+2*w.encode.length+1)^2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  exact (loop_hoare s hs w hm initial).mono_bound hb

theorem activation_iff (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) :
    (∀ r, w.values s.reactions r ≠ 0 → s.toSource.sideAdmissible (w.entities s.entities) r) ↔
      ∀ r : Fin s.reactions, w.values s.reactions r ≠ 0 →
        (flags s w).getD r.val false = true ∧
          (flags s w).getD (s.reactions+r.val) false = true := by
  simp_rw [VerifierActivationSemantics.sideAdmissible_iff,left_flag,right_flag]

end UnconstrainedPACDetection.VerifierActivationSource

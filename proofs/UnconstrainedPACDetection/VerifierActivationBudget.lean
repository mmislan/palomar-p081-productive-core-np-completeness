module

public import proofs.UnconstrainedPACDetection.VerifierActivationLoop

@[expose] public section

namespace UnconstrainedPACDetection.VerifierActivationBudget
open Complexity Complexity.TM
open VerifierActivationLoop (Row suffix emitted)
open VerifierActivationBody (pred)
open VerifierBufferedProduct (wordTape)

def wire (rows : List Row) : ℕ :=
  (BinaryFields.encode (rows.flatMap (fun es => es.map Prod.fst))).length

def cost (es : Row) : ℕ := (BinaryFields.encode (es.map Prod.fst)).length+4*es.length+10

def total : List Row → ℕ
  | [] => 0
  | es :: rows => cost es + total rows

theorem row_length_le (es : Row) : es.length ≤ (BinaryFields.encode (es.map Prod.fst)).length := by
  induction es with
  | nil => simp [BinaryFields.encode]
  | cons e es ih =>
    simp only [List.map_cons,BinaryFields.encode,List.flatMap_cons,List.length_append,
      BinaryFields.encodeField_length,List.length_cons]
    simp only [BinaryFields.encode] at ih
    omega

theorem cost_le_total (rows : List Row) (es : Row) (h : es ∈ rows) : cost es ≤ total rows := by
  induction rows with
  | nil => simp at h
  | cons e rows ih =>
    rcases List.mem_cons.mp h with he | ht
    · subst es; simp only [total]; omega
    · have hh := ih ht; simp only [total]; omega

theorem wire_cons (es : Row) (rows : List Row) :
    wire (es :: rows) = (BinaryFields.encode (es.map Prod.fst)).length + wire rows := by
  simp [wire,BinaryFields.encode,List.flatMap_append]

theorem total_bound (rows : List Row) : total rows ≤ 5*wire rows+10*rows.length := by
  induction rows with
  | nil => simp [total,wire,BinaryFields.encode]
  | cons es rows ih =>
    have he := row_length_le es
    simp only [total,cost,wire_cons,List.length_cons]
    omega

theorem runtime_bound (rows : List Row) :
    rows.length*(total rows+2)+(rows.length+2) ≤ 20*(wire rows+rows.length+1)^2 := by
  have ht := Nat.mul_le_mul_left rows.length (total_bound rows)
  nlinarith [sq_nonneg (wire rows : ℤ),sq_nonneg (rows.length : ℤ)]

theorem emitted_eq (rows : List Row) (initial : List Bool) (i : ℕ) (hi : i ≤ rows.length) :
    emitted rows initial i = initial ++ (rows.take i).map (fun es => VerifierActivationSide.hit es false) := by
  induction i with
  | zero => simp [emitted]
  | succ i ih =>
    have hil : i < rows.length := by omega
    rw [emitted,ih (by omega),List.take_succ_eq_append_getElem hil,List.map_append]
    simp [List.getD,hil,List.append_assoc]

theorem loop_hoare (rows : List Row) (tail mask witTail initial : List Bool)
    (hm : ∀ es ∈ rows, es.map Prod.snd = mask) :
    VerifierActivationLoop.machine.HoareTime
      (pred (suffix rows tail 0) (wordTape (BinaryFields.encodeField mask ++ witTail))
        (regTape rows.length) initial)
      (pred tail (wordTape (BinaryFields.encodeField mask ++ witTail))
        (regTape rows.length) (initial ++ rows.map (fun es => VerifierActivationSide.hit es false)))
      (20*(wire rows+rows.length+1)^2) := by
  have h := (VerifierActivationLoop.loop_hoare rows tail mask witTail initial (total rows) hm
    (fun es he => cost_le_total rows es he)).mono_bound (runtime_bound rows)
  simpa only [emitted_eq rows initial rows.length le_rfl,List.take_length] using h

end UnconstrainedPACDetection.VerifierActivationBudget

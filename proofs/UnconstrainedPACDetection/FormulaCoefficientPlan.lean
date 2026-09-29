module

public import proofs.UnconstrainedPACDetection.FormulaOrderedTable
public import proofs.UnconstrainedPACDetection.FormulaCoefficientField

@[expose] public section

namespace UnconstrainedPACDetection.FormulaCoefficientPlan
open Complexity Complexity.TM DirectedLinkageSource
open VerifierPairRestore (word word_parked)

inductive Plan where
  | zero | one | two | four | equal (double : Bool)
  deriving DecidableEq, Fintype

def choose (right : Bool) (r a b : Option Bool) : Plan :=
  match r with
  | some false => match a with
    | none => .zero
    | some s => if right == s then .one else .zero
  | some true => match b with
    | none => .zero
    | some s => if right == s then
        if s then (if a == some true then .four else .two)
        else (if a == some true then .two else .one)
      else .zero
  | none => if right then
      match b with | none => .equal (a == some true) | some _ => .zero
    else match a with | none => .equal false | some _ => .zero

def value (p : Plan) (r e : Nat) : Nat := match p with
  | .zero => 0 | .one => 1 | .two => 2 | .four => 4
  | .equal d => FormulaCoefficientField.amount d (decide (r=e))

def machine (p : Plan) : TM 4 := match p with
  | .zero => emitBitsTM (BinaryFields.encodeField (0 : Nat).bits)
  | .one => emitBitsTM (BinaryFields.encodeField (1 : Nat).bits)
  | .two => emitBitsTM (BinaryFields.encodeField (2 : Nat).bits)
  | .four => emitBitsTM (BinaryFields.encodeField (4 : Nat).bits)
  | .equal d => seqTM FormulaClauseCompare.machine (FormulaCoefficientField.machine d)

/-- Each finite coefficient case consumes live indices and restores its complete frame. -/
theorem operation_hoare (p : Plan) (r e : Nat) (ys : List Bool) (inp : Tape)
    (hi : Parked inp) : (machine p).HoareTime
      (EmitPred inp (FormulaClauseCompare.bank r e [true]) ys)
      (EmitPred inp (FormulaClauseCompare.bank r e [true])
        (ys ++ BinaryFields.encodeField (value p r e).bits)) (3*max r e+27) := by
  have hp := FormulaClauseCompare.bank_parked r e [true]
  cases p with
  | zero => exact (emitBitsTM_hoareTime _ _ _ _ hi hp).mono_bound (by change 1 ≤ 3*max r e+27; omega)
  | one => exact (emitBitsTM_hoareTime _ _ _ _ hi hp).mono_bound (by change 3 ≤ 3*max r e+27; omega)
  | two => exact (emitBitsTM_hoareTime _ _ _ _ hi hp).mono_bound (by change 5 ≤ 3*max r e+27; omega)
  | four => exact (emitBitsTM_hoareTime _ _ _ _ hi hp).mono_bound (by change 7 ≤ 3*max r e+27; omega)
  | equal d =>
    have hc := FormulaClauseCompare.compare_hoare r e [true] ys inp hi
    simp only [List.isEmpty_cons,Bool.not_false,Bool.and_true] at hc
    have hf := FormulaCoefficientField.field_hoare d (decide (r=e)) inp
      (FormulaClauseCompare.bank r e [true]) ys hi hp
    exact seqTM_hoareTime _ _ hc (emitPred_transition hi hp _) hf

def tag {X : Type*} : Bool ⊕ X → Option Bool
  | .inl b => some b | .inr _ => none

def index {n : Nat} {T : (Bool ⊕ Bool) ↪ Fin n} : Bool ⊕ MarkedGraph.Internal T → Nat
  | .inl _ => 0 | .inr x => x.val.val

/-- No index equality is used to choose a plan; only finite constructor tags are read. -/
theorem coefficient_value {n : Nat} (T : (Bool ⊕ Bool) ↪ Fin n) (right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal T) (hne : tailRow a ≠ headRow b) :
    value (choose right (tag r) (tag a) (tag b)) (index r)
      (index (if right then b else a)) = FormulaOrderedTable.coefficient T right r (a,b) := by
  have he (x y : MarkedGraph.Internal T) : (x.val.val = y.val.val) ↔ x = y := by
    constructor
    · intro h; apply Subtype.ext; exact Fin.ext h
    · rintro rfl; rfl
  cases right <;> rcases r with (_ | _) | r <;>
    rcases a with (_ | _) | a <;> rcases b with (_ | _) | b
  all_goals simp [value,choose,tag,index,FormulaCoefficientField.amount,
    FormulaOrderedTable.coefficient,tailRow,headRow,tailSign,headSign,factor] at hne ⊢
  all_goals split_ifs <;> simp_all

/-- The actual emitted field is the canonical source coefficient on each legal arc. -/
theorem coefficient_hoare {n : Nat} (T : (Bool ⊕ Bool) ↪ Fin n) (right : Bool)
    (r a b : Bool ⊕ MarkedGraph.Internal T) (hne : tailRow a ≠ headRow b)
    (ys : List Bool) (inp : Tape) (hi : Parked inp) :
    (machine (choose right (tag r) (tag a) (tag b))).HoareTime
      (EmitPred inp (FormulaClauseCompare.bank (index r) (index (if right then b else a)) [true]) ys)
      (EmitPred inp (FormulaClauseCompare.bank (index r) (index (if right then b else a)) [true])
        (ys ++ BinaryFields.encodeField (FormulaOrderedTable.coefficient T right r (a,b)).bits))
      (3*max (index r) (index (if right then b else a))+27) := by
  simpa only [coefficient_value T right r a b hne] using
    operation_hoare (choose right (tag r) (tag a) (tag b))
      (index r) (index (if right then b else a)) ys inp hi

end UnconstrainedPACDetection.FormulaCoefficientPlan

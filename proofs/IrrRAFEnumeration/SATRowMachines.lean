module

public import proofs.IrrRAFEnumeration.SATBoundaryRows
public import proofs.IrrRAFEnumeration.SATMachineRuns

@[expose] public section

namespace IrrRAFEnumeration.SATSource

open Complexity Complexity.TM

def spanRowTM {k : Nat} (before count after : Fin k) : TM k :=
  seqTM (emitRunTM false before) (seqTM (emitRunTM true count) (emitRunTM false after))

theorem spanRowTM_correct {k : Nat} (ra rb rc : Fin k) (a b c : Nat)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hip : Parked inp) (hwp : ∀ i, Parked (work i))
    (ha : work ra = regTape a) (hb : work rb = regTape b) (hc : work rc = regTape c) :
    (spanRowTM ra rb rc).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys ++ spanRow a b c)) (4*(a+b+c)+8) := by
  have h₁ := emitRunTM_correct false ra a inp work ys hip hwp ha
  have h₂ := emitRunTM_correct true rb b inp work (ys ++ List.replicate a false) hip hwp hb
  have h₃ := emitRunTM_correct false rc c inp work
    ((ys ++ List.replicate a false) ++ List.replicate b true) hip hwp hc
  have h₂₃ := seqTM_hoareTime _ _ h₂
    (emitPred_transition hip hwp _) h₃
  have hall := seqTM_hoareTime _ _ h₁
    (emitPred_transition hip hwp _) h₂₃
  have htime : (4*a+2)+1+((4*b+2)+1+(4*c+2)) = 4*(a+b+c)+8 := by omega
  simpa only [spanRowTM, spanRow, List.append_assoc, htime] using hall

def markedRowTM {k : Nat} (before bit between after : Fin k) : TM k :=
  seqTM (emitRunTM false before)
    (seqTM (emitRegisterBitTM bit)
      (seqTM (emitRunTM false between)
        (seqTM (emitBitsTM [true]) (emitRunTM false after))))

/-- Emit an optional signal mark and its mandatory private marker. The bit is
read from a register; it is not hardwired into an instance-dependent machine. -/
theorem markedRowTM_correct {k : Nat} (ra rbit rb rc : Fin k) (a b c : Nat) (bit : Bool)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hip : Parked inp) (hwp : ∀ i, Parked (work i))
    (ha : work ra = regTape a) (hb : work rb = regTape b) (hc : work rc = regTape c)
    (hbit : work rbit = regTape (if bit then 1 else 0)) :
    (markedRowTM ra rbit rb rc).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys ++ markedRow a b c bit)) (4*(a+b+c)+12) := by
  have h₁ := emitRunTM_correct false ra a inp work ys hip hwp ha
  have h₂ := emitRegisterBitTM_correct rbit bit inp work
    (ys ++ List.replicate a false) hip hwp hbit
  have h₃ := emitRunTM_correct false rb b inp work
    ((ys ++ List.replicate a false) ++ [bit]) hip hwp hb
  have h₄ := emitBitsTM_hoareTime [true] inp work
    (((ys ++ List.replicate a false) ++ [bit]) ++ List.replicate b false) hip hwp
  have h₅ := emitRunTM_correct false rc c inp work
    ((((ys ++ List.replicate a false) ++ [bit]) ++ List.replicate b false) ++ [true]) hip hwp hc
  have h₄₅ := seqTM_hoareTime _ _ h₄ (emitPred_transition hip hwp _) h₅
  have h₃₄₅ := seqTM_hoareTime _ _ h₃ (emitPred_transition hip hwp _) h₄₅
  have h₂₃₄₅ := seqTM_hoareTime _ _ h₂ (emitPred_transition hip hwp _) h₃₄₅
  have hall := seqTM_hoareTime _ _ h₁ (emitPred_transition hip hwp _) h₂₃₄₅
  have htime : (4*a+2)+1+(1+1+((4*b+2)+1+(1+1+(4*c+2)))) = 4*(a+b+c)+12 := by omega
  simpa only [markedRowTM, markedRow, List.length_singleton, List.append_assoc, htime] using hall

def blockLastRowTM {k : Nat} (before count after : Fin k) : TM k :=
  seqTM (spanRowTM before count after) (emitBitsTM [true])

theorem blockLastRowTM_correct {k : Nat} (ra rb rc : Fin k) (a b c : Nat)
    (inp : Tape) (work : Fin k → Tape) (ys : List Bool)
    (hip : Parked inp) (hwp : ∀ i, Parked (work i))
    (ha : work ra = regTape a) (hb : work rb = regTape b) (hc : work rc = regTape c) :
    (blockLastRowTM ra rb rc).HoareTime (EmitPred inp work ys)
      (EmitPred inp work (ys ++ blockLastRow a b c)) (4*(a+b+c)+10) := by
  have h₁ := spanRowTM_correct ra rb rc a b c inp work ys hip hwp ha hb hc
  have h₂ := emitBitsTM_hoareTime [true] inp work (ys ++ spanRow a b c) hip hwp
  have hall := seqTM_hoareTime _ _ h₁ (emitPred_transition hip hwp _) h₂
  unfold EmitPred at hall ⊢
  simpa [blockLastRowTM, blockLastRow, List.append_assoc, Nat.add_assoc] using hall

end IrrRAFEnumeration.SATSource

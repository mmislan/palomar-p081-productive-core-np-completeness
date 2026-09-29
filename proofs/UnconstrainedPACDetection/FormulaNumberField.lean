module

public import proofs.UnconstrainedPACDetection.FormulaHeaderConversion
public import proofs.UnconstrainedPACDetection.FormulaFieldEmission

@[expose] public section

namespace UnconstrainedPACDetection.FormulaNumberField
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open VerifierPairRestore (word word_parked)

def bank (v : Nat) : Fin 3 → Tape := ![word v.bits,word [true],regTape v]

theorem bank_parked (v : Nat) : ∀ j, Parked (bank v j) := by
  intro j
  fin_cases j
  · exact word_parked _
  · exact word_parked _
  · exact parked_regTape _

@[reducible] def append : TM 3 := placeWorkTM 0 2 FormulaFieldEmission.machine

theorem append_hoare (v : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    append.HoareTime (EmitPred inp (bank v) ys)
      (EmitPred inp (bank v) (ys ++ BinaryFields.encodeField v.bits)) (3*v.bits.length+5) := by
  rintro i w o ⟨hin,hw,ho⟩
  subst i; subst w
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := FormulaFieldEmission.field_hoare v.bits ys inp hi
    inp (fun _ => word v.bits) o ⟨rfl,rfl,ho⟩
  have hs := placeWorkTM_reachesIn_placeWorkCfg_stable_internal
    FormulaFieldEmission.machine 0 2 (bank v) hr
    (by intro j _; exact (bank_parked v j).read_ne_start)
  refine ⟨placeWorkCfg _ 0 2 (bank v) d,t,ht,?_,hh,hdi,?_,hdo⟩
  · convert hs using 1
    apply Cfg.ext
    · rfl
    · rfl
    · funext j; fin_cases j <;> rfl
    · rfl
  · funext j
    fin_cases j <;> simp [placeWorkCfg,placeWorkInMiddle,placeWorkCoord,bank,hdw]

@[reducible] def machine : TM 3 := seqTM VerifierCountPrepare.machine append

/-- Live unary value to its exact canonical field, retaining its register and binary word. -/
theorem field_hoare (v : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    machine.HoareTime (EmitPred inp (VerifierCountPrepare.initial v) ys)
      (EmitPred inp (bank v) (ys ++ BinaryFields.encodeField v.bits))
      (20*(v+1)^2+3*v.bits.length+8) := by
  have hc : VerifierCountPrepare.machine.HoareTime
      (EmitPred inp (VerifierCountPrepare.initial v) ys)
      (EmitPred inp (bank v) ys) (20*(v+1)^2+2) :=
    FormulaHeaderConversion.canonical_hoare v inp hi ys
  have h := seqTM_hoareTime _ _ hc (emitPred_transition hi (bank_parked v) ys)
    (append_hoare v inp hi ys)
  exact h.mono_bound (by omega)

theorem field_bounded (v : Nat) (inp : Tape) (hi : Parked inp) (ys : List Bool) :
    machine.HoareTime (EmitPred inp (VerifierCountPrepare.initial v) ys)
      (EmitPred inp (bank v) (ys ++ BinaryFields.encodeField v.bits))
      (24*(v+1)^2+8) := by
  have hl := VerifierUnaryBinary.digits_length v
  rw [FormulaHeaderBinaryDigits.digits_eq_bits] at hl
  exact (field_hoare v inp hi ys).mono_bound (by nlinarith)

end UnconstrainedPACDetection.FormulaNumberField

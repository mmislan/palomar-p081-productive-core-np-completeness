module

public import proofs.UnconstrainedPACDetection.FormulaReactionRegisters
public import proofs.UnconstrainedPACDetection.FormulaReactionField
public import proofs.UnconstrainedPACDetection.VerifierTapeCleanup

@[expose] public section

namespace UnconstrainedPACDetection.FormulaReactionFinish
open Complexity Complexity.TM
open VerifierPairRestore (word word_parked updated_parked)

theorem cleanup_emit {n : Nat} (j : Fin n) (xs ys : List Bool)
    (inp : Tape) (w : Fin n → Tape) (hi : Parked inp) (hp : ∀ k, Parked (w k))
    (hc : (w j).cells = (word xs).cells) :
    (VerifierTapeCleanup.machine j).HoareTime (EmitPred inp w ys)
      (EmitPred inp (Function.update w j (word [])) ys)
      ((w j).head+2*xs.length+8) := by
  rintro i ws o ⟨hin,hw,ho⟩
  subst i; subst ws
  obtain ⟨d,t,ht,hr,hh,hdi,hdw,hdo⟩ := VerifierTapeCleanup.cleanup_hoare j xs w inp o hc
    (fun k => ⟨(hp k).read_ne_start,(hp k).1⟩) hi.read_ne_start
    ho.parked.read_ne_start ho.parked.1 inp w o ⟨rfl,rfl,rfl⟩
  exact ⟨d,t,ht,hr,hh,hdi,hdw,hdo ▸ ho⟩

def clean : TM 7 := seqTM (VerifierTapeCleanup.machine 3) (VerifierTapeCleanup.machine 6)
def cleanBank (w : Fin 7 → Tape) : Fin 7 → Tape :=
  Function.update (Function.update w 3 (word [])) 6 (word [])

theorem clean_parked (w : Fin 7 → Tape) (hp : ∀ j, Parked (w j)) :
    ∀ j, Parked (cleanBank w j) :=
  updated_parked _ 6 [] (updated_parked w 3 [] hp)

theorem clean_hoare (xs bs ys : List Bool) (inp : Tape) (w : Fin 7 → Tape)
    (hi : Parked inp) (hp : ∀ j, Parked (w j))
    (h3 : OutAcc xs (w 3)) (h6 : w 6 = word bs) :
    clean.HoareTime (EmitPred inp w ys) (EmitPred inp (cleanBank w) ys)
      (3*xs.length+2*bs.length+19) := by
  have hfirst := cleanup_emit 3 xs ys inp w hi hp (VerifierPairRestore.acc_cells xs _ h3)
  have hsecond := cleanup_emit 6 bs ys inp (Function.update w 3 (word [])) hi
    (updated_parked w 3 [] hp) (by simp [h6])
  have h := seqTM_hoareTime _ _ hfirst
    (emitPred_transition hi (updated_parked w 3 [] hp) ys) hsecond
  apply h.mono_bound
  simp only [Function.update_of_ne (by decide : (6 : Fin 7) ≠ 3),h6]
  change (w 3).head + 2*xs.length+8+1+(1+2*bs.length+8) ≤ _
  have hh := h3.1
  omega

def machine : TM 7 := seqTM FormulaReactionRegisters.machine
  (seqTM clean FormulaReactionField.emit)

def finalBank (w : Fin 7 → Tape) (r : Nat) : Fin 7 → Tape :=
  FormulaReactionField.afterWork (cleanBank (FormulaReactionRegisters.bank w r)) r

theorem finish_hoare (c o v M : Nat) (xs bs ys : List Bool)
    (inp : Tape) (w : Fin 7 → Tape) (hi : Parked inp) (hp : ∀ j, Parked (w j))
    (h0 : w 0 = regTape c) (h1 : w 1 = regTape o) (h2 : w 2 = regTape v)
    (h3 : OutAcc xs (w 3)) (h5 : w 5 = regTape 1) (h6 : w 6 = word bs)
    (hc : c ≤ M) (ho : o ≤ M) (hv : v ≤ M)
    (hr : FormulaReactionRegisters.value c o v ≤ M) :
    machine.HoareTime (EmitPred inp w ys)
      (EmitPred inp (finalBank w (FormulaReactionRegisters.value c o v))
        (ys ++ BinaryFields.encodeField (FormulaReactionRegisters.value c o v).bits))
      (40*(opBudget M+1)+3*xs.length+2*bs.length+
        24*(FormulaReactionRegisters.value c o v+1)^2+30) := by
  let r := FormulaReactionRegisters.value c o v
  let W := FormulaReactionRegisters.bank w r
  have hpW := FormulaReactionRegisters.bank_parked w hp r
  have ha := FormulaReactionRegisters.arithmetic_hoare c o v M inp w ys hi hp
    h0 h1 h2 h5 hc ho hv hr
  have hb := clean_hoare xs bs ys inp W hi hpW
    (by simpa [W,FormulaReactionRegisters.bank] using h3)
    (by simpa [W,FormulaReactionRegisters.bank] using h6)
  have he := FormulaReactionField.emit_hoare r inp (cleanBank W) ys hi
    (clean_parked W hpW) (by simp [cleanBank,W,FormulaReactionRegisters.bank])
    (by simp [cleanBank]) (by simp [cleanBank])
  have hbe := seqTM_hoareTime _ _ hb (emitPred_transition hi (clean_parked W hpW) ys) he
  have h := seqTM_hoareTime _ _ ha (emitPred_transition hi hpW ys) hbe
  exact h.mono_bound (by dsimp [r]; omega)

end UnconstrainedPACDetection.FormulaReactionFinish

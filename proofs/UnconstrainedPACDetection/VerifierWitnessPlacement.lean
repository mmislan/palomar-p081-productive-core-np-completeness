module

public import proofs.UnconstrainedPACDetection.VerifierPreparedCertificate
public import proofs.IrrRAFEnumeration.CompletionInitialCopy

@[expose] public section

namespace UnconstrainedPACDetection.VerifierWitnessPlacement
open Complexity Complexity.TM
open VerifierBufferedProduct (wordTape)
open IrrRAFEnumeration.CompletionQuery (copyParkedBufferTM copyParkedBuffer_correct)
open IrrRAFEnumeration.SATSource (parkedInput)

def restored (work : Fin 30 → Tape) (bits : List Bool) :=
  Function.update work 27 (wordTape bits)

def placed (work : Fin 30 → Tape) (bits : List Bool) :=
  Function.update (Function.update (restored work bits) 4 (wordTape bits)) 14 (wordTape bits)

theorem updated_parked {n : Nat} (work : Fin n → Tape) (i : Fin n) (bits : List Bool)
    (hw : ∀ j, Parked (work j)) : ∀ j, Parked (Function.update work i (wordTape bits) j) := by
  intro j
  by_cases hj : j = i
  · subst j; simpa using VerifierReactionLoop.word_parked bits
  · simpa only [Function.update_of_ne hj] using hw j

theorem rewind_hoare (bits : List Bool) (inp : Tape) (work : Fin 30 → Tape) (B : Nat)
    (hi : Parked inp) (hw : ∀ j, Parked (work j))
    (hc : (work 27).cells = (wordTape bits).cells) (hb : (work 27).head ≤ B) :
    (rewindWorkTM (27 : Fin 30)).HoareTime (EmitPred inp work [])
      (EmitPred inp (restored work bits) []) (B+2) := by
  let P : Complexity.TM.TapePred 30 := fun a ws out => a = inp ∧
    (ws 27).cells = (wordTape bits).cells ∧
    (∀ j, j ≠ 27 → ws j = work j) ∧ OutAcc [] out
  have h := rewindWorkTM_hoareTime_frame (27 : Fin 30) B (P := P) (by
    rintro a ws out a' ws' out' ⟨ha,hcells,hother,ho⟩ hc' _ hw' hi' ho' hh'
    exact ⟨hi'.trans ha,hc'.trans hcells,fun j hj => (hw' j hj).trans (hother j hj),
      (Tape.ext hh' ho').symm ▸ ho⟩)
  apply h.consequence
  · rintro a ws out ⟨ha,hws,ho⟩
    subst a; subst ws
    refine ⟨?_,(hw 27).2,hb,hi.read_ne_start,ho.parked.read_ne_start,ho.parked.1,
      fun j _ => ⟨(hw j).read_ne_start,(hw j).1⟩,rfl,hc,fun _ _ => rfl,ho⟩
    rw [hc]; rfl
  · rintro a ws out ⟨hh,ha,hcells,hother,ho⟩
    refine ⟨ha,?_,ho⟩
    funext j
    by_cases hj : j = 27
    · subst j
      exact Tape.ext hh hcells
    · simpa only [restored,Function.update_of_ne hj] using hother j hj
  · rfl

/-- Raw validation lives in tapes 18..28; its witness is tape 27.
Copy it into the actual productivity and activation witness slots, restoring
all three witness heads and preserving every unrelated tape. -/
def machine : TM 30 := seqTM (rewindWorkTM (27 : Fin 30))
  (seqTM (copyParkedBufferTM (27 : Fin 30) 4) (copyParkedBufferTM (27 : Fin 30) 14))

theorem placement_hoare (bits : List Bool) (inp : Tape) (work : Fin 30 → Tape) (B : Nat)
    (hi : Parked inp) (hw : ∀ j, Parked (work j))
    (hc : (work 27).cells = (wordTape bits).cells) (hb : (work 27).head ≤ B)
    (h4 : work 4 = regTape 0) (h14 : work 14 = regTape 0) :
    machine.HoareTime (EmitPred inp work []) (EmitPred inp (placed work bits) [])
      (B+6*bits.length+22) := by
  let W := restored work bits
  let V := Function.update W 4 (wordTape bits)
  have hpW : ∀ j, Parked (W j) := updated_parked work 27 bits hw
  have hpV : ∀ j, Parked (V j) := updated_parked W 4 bits hpW
  have he : parkedInput bits = wordTape bits := rfl
  have hfirst := copyParkedBuffer_correct (27 : Fin 30) 4 (by decide)
    bits inp W hi hpW (by rw [he]; rfl) (by exact h4)
  have hsecond := copyParkedBuffer_correct (27 : Fin 30) 14 (by decide)
    bits inp V hi hpV (by rw [he]; rfl) (by exact h14)
  rw [he] at hfirst hsecond
  have htail := seqTM_hoareTime _ _ hfirst
    (emitPred_transition hi hpV []) hsecond
  have htotal := seqTM_hoareTime _ _ (rewind_hoare bits inp work B hi hw hc hb)
    (emitPred_transition hi hpW []) htail
  exact htotal.mono_bound (by omega)

theorem kernel_witness_slots (s : BinarySourceData.DenseSource) (w : BinaryWitnessData.Witness) :
    VerifierPreparedLayout.join (VerifierPreparedCertificate.frame s w 2)
      (VerifierActivationProduce.frame s w (wordTape [])) 4 = wordTape w.encode ∧
    VerifierPreparedLayout.join (VerifierPreparedCertificate.frame s w 2)
      (VerifierActivationProduce.frame s w (wordTape [])) 14 = wordTape w.encode := by
  constructor <;> rfl

end UnconstrainedPACDetection.VerifierWitnessPlacement
